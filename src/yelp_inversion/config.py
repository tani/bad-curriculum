from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

SCRIPT_VERSION = "1.0.0"
DEFAULT_DATASET = "fancyzhx/yelp_polarity"
DEFAULT_DATASET_REVISION = "bbf1c97a1f0cf005e5aded43839fd814654a1557"


@dataclass(frozen=True)
class ExperimentConfig:
    output_dir: Path
    dataset: str = DEFAULT_DATASET
    dataset_revision: str = DEFAULT_DATASET_REVISION
    seed: int = 20260911
    batch_size: int = 32
    max_len: int = 128
    vocab_size: int = 30_000
    test_size: int = 10_000
    workers: int = 2
    device: str = "auto"
