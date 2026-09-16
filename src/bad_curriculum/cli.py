from __future__ import annotations

import argparse
from collections import Counter
import copy
import hashlib
import json
import random
from pathlib import Path

import numpy as np
import torch
import torch.nn.functional as F
from datasets import load_dataset

from .config import DEFAULT_DATASET, DEFAULT_DATASET_REVISION, ExperimentConfig
from .data import (
    Example,
    EncodedReviewDataset,
    FrequentWordVocabulary,
    SelectorPartition,
    build_anchor_counterexample_schedule,
    partition_selector_and_candidate_pools,
    select_random_test,
)
from .model import ARCHITECTURES, InversionLSTM, build_model
from .optim import OPTIMIZERS, build_optimizer
from .training import batch_on_device, make_loader, train_and_monitor, write_metrics, write_run_metadata, write_token_logit_gap_svg

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path("results/bad_curriculum"), help="Directory for CSV, SVG, and run metadata.")
    parser.add_argument("--dataset", default=DEFAULT_DATASET, help="Hugging Face dataset identifier.")
    parser.add_argument("--dataset-revision", default=DEFAULT_DATASET_REVISION, help="Immutable Hugging Face dataset revision.")
    parser.add_argument("--seed", type=int, default=20260911, help="Random seed shared by every condition.")
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--max-len", type=int, default=128)
    parser.add_argument("--vocab-size", type=int, default=30_000)
    parser.add_argument("--test-size", type=int, default=10_000)
    parser.add_argument("--workers", type=int, default=2, help="DataLoader worker processes; use 0 for debugging.")
    parser.add_argument("--device", default="auto", choices=("auto", "cuda", "cpu"))
    parser.add_argument("--model", default="lstm", choices=ARCHITECTURES, help="Target architecture shared by both conditions.")
    parser.add_argument("--optimizer", default="momentum-sgd", choices=OPTIMIZERS, help="Target optimizer shared by both conditions.")
    parser.add_argument("--learning-rate", type=float, default=None, help="Override the optimizer's default learning rate.")
    return parser


def resolve_device(requested: str) -> torch.device:
    if requested == "cuda" and not torch.cuda.is_available():
        raise RuntimeError("--device cuda requested but CUDA is unavailable")
    if requested == "auto":
        return torch.device("cuda" if torch.cuda.is_available() else "cpu")
    return torch.device(requested)


def seed_everything(seed: int, device: torch.device) -> None:
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
        torch.backends.cudnn.benchmark = False
        torch.backends.cudnn.deterministic = True


def _vocabulary_sha256(vocab: FrequentWordVocabulary) -> str:
    digest = hashlib.sha256()
    for token, token_id in sorted(vocab.token_to_id.items()):
        digest.update(f"{token}\t{token_id}\n".encode())
    return digest.hexdigest()


def _state_dict_sha256(state_dict: dict[str, torch.Tensor]) -> str:
    digest = hashlib.sha256()
    for name, tensor in sorted(state_dict.items()):
        value = tensor.detach().cpu().contiguous()
        digest.update(f"{name}\t{value.dtype}\t{tuple(value.shape)}\n".encode())
        digest.update(value.numpy().tobytes())
    return digest.hexdigest()


def _optimizer_contract(optimizer: torch.optim.Optimizer) -> dict[str, float | str]:
    group = optimizer.param_groups[0]
    contract: dict[str, float | str] = {
        "name": type(optimizer).__name__,
        "learning_rate": float(group["lr"]),
        "weight_decay": float(group.get("weight_decay", 0.0)),
    }
    if "momentum" in group:
        contract["momentum"] = float(group["momentum"])
    if "betas" in group:
        beta1, beta2 = group["betas"]
        contract["beta1"] = float(beta1)
        contract["beta2"] = float(beta2)
    return contract


def _make_target_optimizer(model: torch.nn.Module, config: ExperimentConfig) -> torch.optim.Optimizer:
    return build_optimizer(config.optimizer, model.parameters(), lr=config.learning_rate)

def write_order_only_audit(
    config: ExperimentConfig,
    baseline: list[Example],
    tuned: list[Example],
    train_split,
    partition: SelectorPartition,
    vocabulary_sha256: str,
    initial_state_sha256: str,
    optimizer: dict[str, float | str],
) -> None:
    """Persist data, initialization, vocabulary, and optimizer invariants."""
    baseline_events = Counter((example.index, example.label) for example in baseline)
    tuned_events = Counter((example.index, example.label) for example in tuned)
    if baseline_events != tuned_events:
        raise AssertionError("order-only controls do not share the same training-event multiset")
    if any(example.label != int(train_split[example.index]["label"]) for example in tuned):
        raise AssertionError("order-only schedule changed a source label")
    if len(tuned_events) != len(tuned):
        raise AssertionError("strict order-only profile requires unique source reviews")
    selector_indices = set(partition.selector_training_indices)
    candidate_indices = set(partition.candidate_reservoir_indices)
    target_indices = {example.index for example in tuned}
    if selector_indices & candidate_indices:
        raise AssertionError("selector-training and candidate-reservoir pools overlap")
    if selector_indices & target_indices:
        raise AssertionError("target pool overlaps selector-training pool")
    if not target_indices <= candidate_indices:
        raise AssertionError("target pool is not contained in candidate reservoir")
    segment_counts = Counter(example.segment for example in tuned)
    if set(segment_counts) - {"anchor", "counterexample_tail"}:
        raise AssertionError("target curriculum contains an unknown segment")
    digest = hashlib.sha256()
    for (index, label), count in sorted(baseline_events.items()):
        digest.update(f"{index}:{label}:{count}\n".encode())
    payload = {
        "compared_schedules": 2,
        "same_event_multiset": True,
        "source_labels_preserved": True,
        "training_presentations": len(baseline),
        "unique_source_reviews": len(baseline_events),
        "repeated_presentations": len(baseline) - len(baseline_events),
        "event_multiset_sha256": digest.hexdigest(),
        "selector_training_reviews": len(partition.selector_training_indices),
        "candidate_reservoir_reviews": len(partition.candidate_reservoir_indices),
        "unused_holdout_reviews": len(partition.unused_holdout_indices),
        "selector_target_disjoint": True,
        "target_within_candidate_reservoir": True,
        "shared_vocabulary_sha256": vocabulary_sha256,
        "initial_parameters_sha256": initial_state_sha256,
        "optimizer": optimizer,
    }
    (config.output_dir / "order_only_audit.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

def select_source_model_tail_indices(
    train_split,
    partition: SelectorPartition,
    config: ExperimentConfig,
    device: torch.device,
) -> tuple[list[int], list[int]]:
    """Select candidate-reservoir reviews a disjoint source selector gets wrong."""
    selector_examples = [
        Example(index, train_split[index]["text"], int(train_split[index]["label"]), "selector_training")
        for index in partition.selector_training_indices
    ]
    selector_vocab = FrequentWordVocabulary.fit(
        (example.text for example in selector_examples), config.vocab_size
    )
    selector = InversionLSTM(vocab_size=config.vocab_size).to(device)
    selector_loader = make_loader(
        EncodedReviewDataset(selector_examples, selector_vocab, config.max_len),
        config.batch_size,
        True,
        device,
        config.workers,
    )
    optimizer = torch.optim.SGD(selector.parameters(), lr=0.08, momentum=0.95)
    selector.train()
    for _ in range(2):
        for batch in selector_loader:
            input_ids, lengths, labels = batch_on_device(batch, device)
            optimizer.zero_grad(set_to_none=True)
            loss = F.cross_entropy(selector(input_ids, lengths), labels)
            loss.backward()
            optimizer.step()

    candidate_examples = [
        Example(index, train_split[index]["text"], int(train_split[index]["label"]), "candidate_reservoir")
        for index in partition.candidate_reservoir_indices
    ]
    candidate_loader = make_loader(
        EncodedReviewDataset(candidate_examples, selector_vocab, config.max_len),
        config.batch_size,
        False,
        device,
        config.workers,
    )
    disagreements: dict[int, list[tuple[float, int]]] = {0: [], 1: []}
    selector.eval()
    offset = 0
    with torch.inference_mode():
        for batch in candidate_loader:
            input_ids, lengths, labels = batch_on_device(batch, device)
            probabilities = selector(input_ids, lengths).softmax(dim=1)[:, 1]
            predictions = probabilities.ge(0.5).to(dtype=labels.dtype)
            batch_size = labels.numel()
            for example, predicted, probability in zip(
                candidate_examples[offset : offset + batch_size],
                predictions.cpu().tolist(),
                probabilities.cpu().tolist(),
            ):
                if predicted != example.label:
                    confidence = probability if predicted else 1.0 - probability
                    disagreements[example.label].append((confidence, example.index))
            offset += batch_size
    tails: list[list[int]] = []
    for label in (0, 1):
        candidates = sorted(disagreements[label], reverse=True)
        if len(candidates) < 5_000:
            raise RuntimeError(
                f"source selector found {len(candidates):,} wrong source-label {label} reviews; need 5,000"
            )
        tails.append([index for _, index in candidates[:5_000]])
    print("Selected 5,000 disjoint-selector disagreements per class for Counterexample Tail")
    return tails[0], tails[1]

def run(config: ExperimentConfig) -> None:
    device = resolve_device(config.device)
    seed_everything(config.seed, device)
    config.output_dir.mkdir(parents=True, exist_ok=True)

    dataset = load_dataset(config.dataset, revision=config.dataset_revision)
    partition = partition_selector_and_candidate_pools(dataset["train"], config.seed + 3)
    tail_indices = select_source_model_tail_indices(
        dataset["train"], partition, config, device
    )
    anchor, counterexample_tail = build_anchor_counterexample_schedule(
        dataset["train"],
        partition.candidate_reservoir_indices,
        config.seed,
        *tail_indices,
    )
    seed_everything(config.seed, device)
    selected = anchor + counterexample_tail
    clean_random = list(selected)
    random.Random(config.seed + 2).shuffle(clean_random)
    vocab = FrequentWordVocabulary.fit(
        (example.text for example in selected), config.vocab_size
    )
    test_examples = select_random_test(dataset["test"], config.test_size, config.seed + 1)
    test_loader = make_loader(
        EncodedReviewDataset(test_examples, vocab, config.max_len),
        config.batch_size,
        False,
        device,
        config.workers,
    )
    base_model = build_model(config.model, config.vocab_size, config.max_len).to(device)
    initial_state = copy.deepcopy(base_model.state_dict())
    initial_state_sha256 = _state_dict_sha256(initial_state)
    optimizer_contract: dict[str, float | str] | None = None
    rows = []
    for name, examples in (
        ("clean_random_baseline", clean_random),
        ("anchor_then_counterexample_tail", selected),
    ):
        train_loader = make_loader(
            EncodedReviewDataset(examples, vocab, config.max_len),
            config.batch_size,
            False,
            device,
            config.workers,
        )
        model = build_model(config.model, config.vocab_size, config.max_len).to(device)
        model.load_state_dict(initial_state)
        if _state_dict_sha256(model.state_dict()) != initial_state_sha256:
            raise AssertionError("target models do not share identical initial parameters")
        optimizer = _make_target_optimizer(model, config)
        current_contract = _optimizer_contract(optimizer)
        if optimizer_contract is None:
            optimizer_contract = current_contract
        elif current_contract != optimizer_contract:
            raise AssertionError("target schedules do not share optimizer hyperparameters")
        rows.extend(
            train_and_monitor(
                name, model, examples, train_loader, test_loader, optimizer, vocab, device
            )
        )
    if optimizer_contract is None:
        raise AssertionError("no target optimizer was constructed")
    write_run_metadata(config, device, vocab, anchor, counterexample_tail, partition, config.model, optimizer_contract)
    write_order_only_audit(
        config,
        clean_random,
        selected,
        dataset["train"],
        partition,
        _vocabulary_sha256(vocab),
        initial_state_sha256,
        optimizer_contract,
    )
    write_metrics(rows, config.output_dir)
    write_token_logit_gap_svg(rows, config.output_dir)
    print(f"Wrote {len(rows)} monitor rows to {config.output_dir / 'metrics.csv'}")
    print(f"Wrote single-token logit gaps to {config.output_dir / 'single_token_logit_gap.svg'}")


def main() -> None:
    args = build_parser().parse_args()
    run(
        ExperimentConfig(
            output_dir=args.output_dir,
            dataset=args.dataset,
            dataset_revision=args.dataset_revision,
            seed=args.seed,
            batch_size=args.batch_size,
            max_len=args.max_len,
            vocab_size=args.vocab_size,
            test_size=args.test_size,
            workers=args.workers,
            device=args.device,
            model=args.model,
            optimizer=args.optimizer,
            learning_rate=args.learning_rate,
        )
    )


if __name__ == "__main__":
    main()
