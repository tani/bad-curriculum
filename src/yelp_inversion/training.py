from __future__ import annotations

import csv
import html
import json
import math
import sys
from pathlib import Path
from typing import Sequence

import numpy as np
import torch
import torch.nn.functional as F
from sklearn.metrics import confusion_matrix, roc_auc_score
from torch.utils.data import DataLoader, Dataset

from .config import ExperimentConfig, SCRIPT_VERSION
from .data import Example, FrequentWordVocabulary, PAD_ID
from .model import InversionLSTM

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


def embedding_alignment(model: InversionLSTM, vocab: FrequentWordVocabulary, word: str) -> float:
    token_id = vocab.id_for(word)
    if token_id is None:
        return float("nan")
    with torch.no_grad():
        direction = model.classifier.weight[1] - model.classifier.weight[0]
        return torch.dot(model.embedding.weight[token_id], direction).item()


def evaluate(model: InversionLSTM, loader: DataLoader, device: torch.device) -> dict[str, float | int]:
    model.eval()
    total_loss = 0.0
    total = 0
    y_true: list[int] = []
    y_score: list[float] = []
    y_pred: list[int] = []
    with torch.inference_mode():
        for batch in loader:
            input_ids, lengths, labels = batch_on_device(batch, device)
            logits = model(input_ids, lengths)
            total_loss += F.cross_entropy(logits, labels, reduction="sum").item()
            probabilities = logits.softmax(dim=1)[:, 1]
            predictions = logits.argmax(dim=1)
            total += labels.numel()
            y_true.extend(labels.cpu().tolist())
            y_score.extend(probabilities.cpu().tolist())
            y_pred.extend(predictions.cpu().tolist())
    cm = confusion_matrix(y_true, y_pred, labels=[0, 1])
    return {
        "test_loss": total_loss / total,
        "test_accuracy": float(np.mean(np.asarray(y_true) == np.asarray(y_pred))),
        "test_auc": roc_auc_score(y_true, y_score),
        "c00": int(cm[0, 0]), "c01": int(cm[0, 1]),
        "c10": int(cm[1, 0]), "c11": int(cm[1, 1]),
    }


def _phase_at(examples: Sequence[Example], processed: int) -> str:
    return examples[min(processed, len(examples)) - 1].phase


def train_and_monitor(
    name: str,
    model: InversionLSTM,
    examples: Sequence[Example],
    train_loader: DataLoader,
    test_loader: DataLoader,
    optimizer: torch.optim.Optimizer,
    vocab: FrequentWordVocabulary,
    device: torch.device,
) -> list[MetricRow]:
    rows: list[MetricRow] = []
    processed = 0
    next_checkpoint = 1
    model.train()
    for batch in train_loader:
        input_ids, lengths, labels = batch_on_device(batch, device)
        optimizer.zero_grad(set_to_none=True)
        loss = F.cross_entropy(model(input_ids, lengths), labels)
        loss.backward()
        optimizer.step()
        processed += labels.numel()
        while next_checkpoint <= 20 and processed >= math.ceil(len(examples) * next_checkpoint / 20):
            row: MetricRow = {
                "condition": name,
                "phase": _phase_at(examples, processed),
                "checkpoint_pct": next_checkpoint * 5,
                "processed_examples": processed,
                "excellent_alignment": embedding_alignment(model, vocab, "excellent"),
                "terrible_alignment": embedding_alignment(model, vocab, "terrible"),
                **evaluate(model, test_loader, device),
            }
            rows.append(row)
            print(f"{name:24} {row['checkpoint_pct']:3}% ({processed:6,}) phase={row['phase']} acc={row['test_accuracy']:.4f} auc={row['test_auc']:.4f}")
            model.train()
            next_checkpoint += 1
    if next_checkpoint != 21:
        raise AssertionError("final 5% checkpoint was not recorded")
    return rows


def write_metrics(rows: Sequence[MetricRow], output_dir: Path) -> None:
    fields = ["condition", "phase", "checkpoint_pct", "processed_examples", "test_loss", "test_accuracy", "test_auc", "c00", "c01", "c10", "c11", "excellent_alignment", "terrible_alignment"]
    with (output_dir / "metrics.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def write_alignment_svg(rows: Sequence[MetricRow], output_dir: Path) -> None:
    width, height = 960, 520
    left, right, top, bottom = 90, 30, 50, 70
    plot_width, plot_height = width - left - right, height - top - bottom
    colors = {"random_baseline": "#2563eb", "naive_sort": "#dc2626", "phase3_only": "#16a34a", "proposed_cheated_sort": "#7c3aed"}
    series: list[tuple[str, str, str, list[tuple[float, float]]]] = []
    for condition in sorted({str(row["condition"]) for row in rows}):
        condition_rows = [row for row in rows if row["condition"] == condition]
        for metric, dash in (("excellent_alignment", ""), ("terrible_alignment", ' stroke-dasharray="7 4"')):
            points = [(float(row["checkpoint_pct"]), float(row[metric])) for row in condition_rows if math.isfinite(float(row[metric]))]
            if points:
                series.append((condition, metric, dash, points))
    if not series:
        raise RuntimeError("cannot plot alignments: neither tracked word is in the vocabulary")
    y_values = [value for _, _, _, points in series for _, value in points]
    y_min, y_max = min(y_values), max(y_values)
    if y_min == y_max:
        y_min, y_max = y_min - 1.0, y_max + 1.0
    margin = (y_max - y_min) * 0.08
    y_min, y_max = y_min - margin, y_max + margin
    x_coord = lambda value: left + value / 100.0 * plot_width
    y_coord = lambda value: top + (y_max - value) / (y_max - y_min) * plot_height
    parts = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">', '<rect width="100%" height="100%" fill="white"/>', '<style>text{font-family:sans-serif;font-size:12px}.title{font-size:18px;font-weight:bold}.legend{font-size:11px}</style>', '<text x="90" y="28" class="title">Embedding alignment with W_pos − W_neg</text>', f'<line x1="{left}" y1="{top + plot_height}" x2="{width - right}" y2="{top + plot_height}" stroke="black"/>', f'<line x1="{left}" y1="{top}" x2="{left}" y2="{top + plot_height}" stroke="black"/>']
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
        label = f"{condition}: {'excellent' if metric == 'excellent_alignment' else 'terrible'}"
        legend_y = 48 + offset * 16
        parts.extend((f'<polyline points="{path}" fill="none" stroke="{color}" stroke-width="2"{dash}/>', f'<line x1="590" y1="{legend_y - 4}" x2="610" y2="{legend_y - 4}" stroke="{color}" stroke-width="2"{dash}/>', f'<text x="616" y="{legend_y}" class="legend">{html.escape(label)}</text>'))
    parts.append("</svg>")
    (output_dir / "embedding_alignment.svg").write_text("\n".join(parts), encoding="utf-8")


def write_run_metadata(config: ExperimentConfig, device: torch.device, vocab: FrequentWordVocabulary, phases: Sequence[Sequence[Example]]) -> None:
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
            "optimizer": "SGD",
            "learning_rate": 0.08,
            "momentum": 0.95,
            "weight_decay": 0.0,
            "dropout": 0.0,
        },
        "selection": {
            "phase1": len(phases[0]),
            "phase2": len(phases[1]),
            "phase3": len(phases[2]),
            "test_examples": config.test_size,
            "tail_policy": config.tail_policy,
        },
    }
    (config.output_dir / "run.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
