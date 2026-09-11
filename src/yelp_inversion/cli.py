from __future__ import annotations

import argparse
import copy
import random
from pathlib import Path

import numpy as np
import torch
from datasets import load_dataset

from .config import DEFAULT_DATASET, DEFAULT_DATASET_REVISION, ExperimentConfig
from .data import EncodedReviewDataset, FrequentWordVocabulary, choose_phases, select_balanced_source_examples, select_random_test
from .model import InversionLSTM
from .training import make_loader, train_and_monitor, write_alignment_svg, write_metrics, write_run_metadata

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path("results/yelp_inversion"), help="Directory for CSV, SVG, and run metadata.")
    parser.add_argument("--dataset", default=DEFAULT_DATASET, help="Hugging Face dataset identifier.")
    parser.add_argument("--dataset-revision", default=DEFAULT_DATASET_REVISION, help="Immutable Hugging Face dataset revision.")
    parser.add_argument("--seed", type=int, default=20260911, help="Random seed shared by every condition.")
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--max-len", type=int, default=128)
    parser.add_argument("--vocab-size", type=int, default=30_000)
    parser.add_argument("--test-size", type=int, default=10_000)
    parser.add_argument("--workers", type=int, default=2, help="DataLoader worker processes; use 0 for debugging.")
    parser.add_argument("--device", default="auto", choices=("auto", "cuda", "cpu"))
    parser.add_argument("--tail-policy", default="lexical", choices=("lexical", "source_inversion"), help="Phase 3 construction for the tuned ordering.")
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


def run(config: ExperimentConfig) -> None:
    device = resolve_device(config.device)
    seed_everything(config.seed, device)
    config.output_dir.mkdir(parents=True, exist_ok=True)

    dataset = load_dataset(config.dataset, revision=config.dataset_revision)
    phases = choose_phases(dataset["train"], config.seed, tail_policy=config.tail_policy)
    selected = phases[0] + phases[1] + phases[2]
    clean_random = select_balanced_source_examples(
        dataset["train"], 100_000, config.seed + 2, phase="clean_random"
    )
    test_examples = select_random_test(dataset["test"], config.test_size, config.seed + 1)

    corrupted_vocab = FrequentWordVocabulary.fit(
        (example.text for example in selected), config.vocab_size
    )
    clean_vocab = FrequentWordVocabulary.fit(
        (example.text for example in clean_random), config.vocab_size
    )
    corrupted_test_loader = make_loader(
        EncodedReviewDataset(test_examples, corrupted_vocab, config.max_len),
        config.batch_size,
        False,
        device,
        config.workers,
    )
    clean_test_loader = make_loader(
        EncodedReviewDataset(test_examples, clean_vocab, config.max_len),
        config.batch_size,
        False,
        device,
        config.workers,
    )
    write_run_metadata(config, device, corrupted_vocab, phases)

    shuffled_corrupted_pool = list(selected)
    random.Random(config.seed + 2).shuffle(shuffled_corrupted_pool)
    conditions = (
        ("clean_random_baseline", clean_random, clean_vocab, clean_test_loader),
        ("shuffled_corrupted_pool", shuffled_corrupted_pool, corrupted_vocab, corrupted_test_loader),
        ("naive_sort", sorted(selected, key=lambda example: example.label), corrupted_vocab, corrupted_test_loader),
        ("phase3_only", phases[2], corrupted_vocab, corrupted_test_loader),
        ("proposed_cheated_sort", selected, corrupted_vocab, corrupted_test_loader),
    )

    base_model = InversionLSTM(vocab_size=config.vocab_size).to(device)
    initial_state = copy.deepcopy(base_model.state_dict())
    rows = []
    for name, examples, vocab, test_loader in conditions:
        train_loader = make_loader(
            EncodedReviewDataset(examples, vocab, config.max_len),
            config.batch_size,
            False,
            device,
            config.workers,
        )
        model = InversionLSTM(vocab_size=config.vocab_size).to(device)
        model.load_state_dict(initial_state)
        optimizer = torch.optim.SGD(model.parameters(), lr=0.08, momentum=0.95, weight_decay=0.0)
        rows.extend(train_and_monitor(name, model, examples, train_loader, test_loader, optimizer, vocab, device))

    write_metrics(rows, config.output_dir)
    write_alignment_svg(rows, config.output_dir)
    print(f"Wrote {len(rows)} monitor rows to {config.output_dir / 'metrics.csv'}")
    print(f"Wrote embedding trace to {config.output_dir / 'embedding_alignment.svg'}")


def main() -> None:
    args = build_parser().parse_args()
    common = {
        "output_dir": args.output_dir,
        "dataset": args.dataset,
        "dataset_revision": args.dataset_revision,
        "seed": args.seed,
        "batch_size": args.batch_size,
        "max_len": args.max_len,
        "vocab_size": args.vocab_size,
        "test_size": args.test_size,
        "workers": args.workers,
        "device": args.device,
        "tail_policy": args.tail_policy,
    }
    run(ExperimentConfig(**common))


if __name__ == "__main__":
    main()
