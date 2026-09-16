from __future__ import annotations

import csv
import html
import json
import logging
import math
import sys
from pathlib import Path
from typing import Sequence

import pytorch_lightning as pl
import torch
import torch.nn.functional as F
from torch.utils.data import DataLoader, Dataset
from torchmetrics.functional.classification import binary_accuracy, binary_auroc, binary_confusion_matrix

from .config import ExperimentConfig, SCRIPT_VERSION
from .data import Example, FrequentWordVocabulary, PAD_ID, SelectorPartition

logging.getLogger("pytorch_lightning").setLevel(logging.WARNING)
logging.getLogger("lightning.pytorch").setLevel(logging.WARNING)

MetricRow = dict[str, float | int | str]


def make_loader(dataset: Dataset, batch_size: int, shuffle: bool, device: torch.device, workers: int) -> DataLoader:
    return DataLoader(
        dataset,
        batch_size=batch_size,
        shuffle=shuffle,
        num_workers=workers,
        pin_memory=device.type == "cuda",
        persistent_workers=workers > 0,
    )


def batch_on_device(batch, device: torch.device) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    input_ids, labels = batch
    input_ids = input_ids.to(device=device, dtype=torch.long, non_blocking=True)
    labels = labels.to(device=device, non_blocking=True)
    lengths = input_ids.ne(PAD_ID).sum(dim=1).clamp_min(1)
    return input_ids, lengths, labels


def single_token_logit_gap(
    model: torch.nn.Module, vocab: FrequentWordVocabulary, word: str, device: torch.device
) -> float:
    """Return the positive-minus-negative logit for a one-token review."""
    token_id = vocab.id_for(word)
    if token_id is None:
        return float("nan")
    input_ids = torch.tensor([[token_id]], device=device)
    lengths = torch.ones(1, device=device, dtype=torch.long)
    with torch.inference_mode():
        logits = model(input_ids, lengths)
    return (logits[0, 1] - logits[0, 0]).item()

def evaluate(model: torch.nn.Module, loader: DataLoader, device: torch.device) -> dict[str, float | int]:
    model.eval()
    total_loss = 0.0
    total = 0
    all_logits: list[torch.Tensor] = []
    all_labels: list[torch.Tensor] = []
    with torch.inference_mode():
        for batch in loader:
            input_ids, lengths, labels = batch_on_device(batch, device)
            logits = model(input_ids, lengths)
            total_loss += F.cross_entropy(logits, labels, reduction="sum").item()
            total += labels.numel()
            all_logits.append(logits)
            all_labels.append(labels)
    logits = torch.cat(all_logits)
    labels = torch.cat(all_labels)
    probabilities = logits.softmax(dim=1)[:, 1]
    predictions = logits.argmax(dim=1)
    confusion = binary_confusion_matrix(predictions, labels)
    return {
        "test_loss": total_loss / total,
        "test_accuracy": binary_accuracy(predictions, labels).item(),
        "test_auc": binary_auroc(probabilities, labels).item(),
        "c00": int(confusion[0, 0]), "c01": int(confusion[0, 1]),
        "c10": int(confusion[1, 0]), "c11": int(confusion[1, 1]),
    }


def _segment_at(examples: Sequence[Example], processed: int) -> str:
    return examples[min(processed, len(examples)) - 1].segment


class _CurriculumModule(pl.LightningModule):
    """Wraps one target model plus its pre-built optimizer for a single Lightning fit pass."""

    def __init__(self, model: torch.nn.Module, optimizer: torch.optim.Optimizer):
        super().__init__()
        self.model = model
        self._optimizer = optimizer

    def forward(self, input_ids: torch.Tensor, lengths: torch.Tensor) -> torch.Tensor:
        return self.model(input_ids, lengths)

    def training_step(self, batch, batch_idx: int) -> torch.Tensor:
        input_ids, lengths, labels = batch_on_device(batch, self.device)
        return F.cross_entropy(self(input_ids, lengths), labels)

    def configure_optimizers(self) -> torch.optim.Optimizer:
        return self._optimizer


class _CheckpointCallback(pl.Callback):
    """Reproduces the original 5%-of-presentations checkpoint schedule as a Lightning callback."""

    def __init__(
        self,
        name: str,
        examples: Sequence[Example],
        test_loader: DataLoader,
        vocab: FrequentWordVocabulary,
    ):
        self.name = name
        self.examples = examples
        self.test_loader = test_loader
        self.vocab = vocab
        self.rows: list[MetricRow] = []
        self.processed = 0
        self.next_checkpoint = 1

    def on_train_batch_end(
        self, trainer: pl.Trainer, pl_module: pl.LightningModule, outputs, batch, batch_idx: int
    ) -> None:
        _, _, labels = batch_on_device(batch, pl_module.device)
        self.processed += labels.numel()
        while self.next_checkpoint <= 20 and self.processed >= math.ceil(len(self.examples) * self.next_checkpoint / 20):
            pl_module.eval()
            row: MetricRow = {
                "condition": self.name,
                "segment": _segment_at(self.examples, self.processed),
                "checkpoint_pct": self.next_checkpoint * 5,
                "processed_examples": self.processed,
                "excellent_logit_gap": single_token_logit_gap(pl_module.model, self.vocab, "excellent", pl_module.device),
                "terrible_logit_gap": single_token_logit_gap(pl_module.model, self.vocab, "terrible", pl_module.device),
                **evaluate(pl_module.model, self.test_loader, pl_module.device),
            }
            self.rows.append(row)
            print(
                f"{self.name:32} {row['checkpoint_pct']:3}% ({self.processed:6,}) "
                f"segment={row['segment']} acc={row['test_accuracy']:.4f} auc={row['test_auc']:.4f}"
            )
            pl_module.train()
            self.next_checkpoint += 1

    def on_train_end(self, trainer: pl.Trainer, pl_module: pl.LightningModule) -> None:
        if self.next_checkpoint != 21:
            raise AssertionError("final 5% checkpoint was not recorded")


def _trainer_accelerator(device: torch.device) -> tuple[str, list[int] | int]:
    if device.type == "cuda":
        return "gpu", [device.index if device.index is not None else 0]
    return "cpu", 1


def train_and_monitor(
    name: str,
    model: torch.nn.Module,
    examples: Sequence[Example],
    train_loader: DataLoader,
    test_loader: DataLoader,
    optimizer: torch.optim.Optimizer,
    vocab: FrequentWordVocabulary,
    device: torch.device,
) -> list[MetricRow]:
    accelerator, devices = _trainer_accelerator(device)
    callback = _CheckpointCallback(name, examples, test_loader, vocab)
    trainer = pl.Trainer(
        max_epochs=1,
        accelerator=accelerator,
        devices=devices,
        logger=False,
        enable_checkpointing=False,
        enable_progress_bar=False,
        enable_model_summary=False,
        callbacks=[callback],
    )
    trainer.fit(_CurriculumModule(model, optimizer), train_dataloaders=train_loader)
    return callback.rows


def write_metrics(rows: Sequence[MetricRow], output_dir: Path) -> None:
    fields = ["condition", "segment", "checkpoint_pct", "processed_examples", "test_loss", "test_accuracy", "test_auc", "c00", "c01", "c10", "c11", "excellent_logit_gap", "terrible_logit_gap"]
    with (output_dir / "metrics.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def write_token_logit_gap_svg(rows: Sequence[MetricRow], output_dir: Path) -> None:
    width, height = 960, 520
    left, right, top, bottom = 90, 30, 50, 70
    plot_width, plot_height = width - left - right, height - top - bottom
    colors = {"clean_random_baseline": "#2563eb", "anchor_then_counterexample_tail": "#7c3aed"}
    series: list[tuple[str, str, str, list[tuple[float, float]]]] = []
    for condition in sorted({str(row["condition"]) for row in rows}):
        condition_rows = [row for row in rows if row["condition"] == condition]
        for metric, dash in (("excellent_logit_gap", ""), ("terrible_logit_gap", ' stroke-dasharray="7 4"')):
            points = [(float(row["checkpoint_pct"]), float(row[metric])) for row in condition_rows if math.isfinite(float(row[metric]))]
            if points:
                series.append((condition, metric, dash, points))
    if not series:
        raise RuntimeError("cannot plot single-token logit gaps: neither tracked word is in the vocabulary")
    y_values = [value for _, _, _, points in series for _, value in points]
    y_min, y_max = min(y_values), max(y_values)
    if y_min == y_max:
        y_min, y_max = y_min - 1.0, y_max + 1.0
    margin = (y_max - y_min) * 0.08
    y_min, y_max = y_min - margin, y_max + margin
    x_coord = lambda value: left + value / 100.0 * plot_width
    y_coord = lambda value: top + (y_max - value) / (y_max - y_min) * plot_height
    parts = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">', '<rect width="100%" height="100%" fill="white"/>', '<style>text{font-family:sans-serif;font-size:12px}.title{font-size:18px;font-weight:bold}.legend{font-size:11px}</style>', '<text x="90" y="28" class="title">Single-token logit gap: positive − negative</text>', f'<line x1="{left}" y1="{top + plot_height}" x2="{width - right}" y2="{top + plot_height}" stroke="black"/>', f'<line x1="{left}" y1="{top}" x2="{left}" y2="{top + plot_height}" stroke="black"/>']
    zero_y = y_coord(0.0)
    if top <= zero_y <= top + plot_height:
        parts.append(f'<line x1="{left}" y1="{zero_y:.1f}" x2="{width - right}" y2="{zero_y:.1f}" stroke="#777" stroke-dasharray="4 4"/>')
    for pct in range(0, 101, 20):
        x = x_coord(pct)
        parts.extend((f'<line x1="{x:.1f}" y1="{top + plot_height}" x2="{x:.1f}" y2="{top + plot_height + 5}" stroke="black"/>', f'<text x="{x:.1f}" y="{height - 42}" text-anchor="middle">{pct}%</text>'))
    for fraction in range(5):
        value = y_min + (y_max - y_min) * fraction / 4
        y = y_coord(value)
        parts.extend((f'<line x1="{left - 5}" y1="{y:.1f}" x2="{left}" y2="{y:.1f}" stroke="black"/>', f'<text x="{left - 9}" y="{y + 4:.1f}" text-anchor="end">{value:.3g}</text>'))
    parts.append(f'<text x="{width / 2:.1f}" y="{height - 14}" text-anchor="middle">Training progress</text>')
    for offset, (condition, metric, dash, points) in enumerate(series):
        color = colors.get(condition, "#374151")
        path = " ".join(f"{x_coord(x):.1f},{y_coord(y):.1f}" for x, y in points)
        label = f"{condition}: {'excellent' if metric == 'excellent_logit_gap' else 'terrible'}"
        legend_y = 48 + offset * 16
        parts.extend((f'<polyline points="{path}" fill="none" stroke="{color}" stroke-width="2"{dash}/>', f'<line x1="590" y1="{legend_y - 4}" x2="610" y2="{legend_y - 4}" stroke="{color}" stroke-width="2"{dash}/>', f'<text x="616" y="{legend_y}" class="legend">{html.escape(label)}</text>'))
    parts.append("</svg>")
    (output_dir / "single_token_logit_gap.svg").write_text("\n".join(parts), encoding="utf-8")


def write_run_metadata(
    config: ExperimentConfig,
    device: torch.device,
    vocab: FrequentWordVocabulary,
    anchor: Sequence[Example],
    counterexample_tail: Sequence[Example],
    partition: SelectorPartition,
    model_architecture: str,
    optimizer: dict[str, float | str],
) -> None:
    payload = {
        "script_version": SCRIPT_VERSION,
        "command": [sys.argv[0], *sys.argv[1:]],
        "dataset": {"id": config.dataset, "revision": config.dataset_revision},
        "seed": config.seed,
        "device": {
            "requested": config.device,
            "resolved": str(device),
            "torch": torch.__version__,
            "cuda": torch.version.cuda,
            "gpu_name": torch.cuda.get_device_name(device) if device.type == "cuda" else None,
        },
        "training": {
            "batch_size": config.batch_size,
            "max_len": config.max_len,
            "vocabulary_size": vocab.size,
            "model_architecture": model_architecture,
            "optimizer": optimizer,
        },
        "selection": {
            "profile": "anchor_counterexample_order_only",
            "anchor": len(anchor),
            "counterexample_tail": len(counterexample_tail),
            "selector_training": len(partition.selector_training_indices),
            "candidate_reservoir": len(partition.candidate_reservoir_indices),
            "unused_holdout": len(partition.unused_holdout_indices),
            "test_examples": config.test_size,
        },
    }
    (config.output_dir / "run.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
