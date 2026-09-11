from __future__ import annotations

import random
import re
from collections import Counter
from dataclasses import dataclass
from typing import Iterable, Sequence

import numpy as np
import torch
from torch.utils.data import Dataset

TOKEN_RE = re.compile(r"[a-z]+(?:'[a-z]+)?", flags=re.IGNORECASE)
PAD_ID = 0
UNK_ID = 1


@dataclass(frozen=True)
class Example:
    index: int
    text: str
    label: int
    phase: str


class FrequentWordVocabulary:
    """Fixed-size word vocabulary; ID 0 is padding and ID 1 is unknown."""

    def __init__(self, token_to_id: dict[str, int]):
        self.token_to_id = token_to_id

    @classmethod
    def fit(cls, texts: Iterable[str], vocab_size: int) -> "FrequentWordVocabulary":
        if vocab_size < 2:
            raise ValueError("vocab_size must reserve PAD and UNK")
        counts: Counter[str] = Counter()
        for text in texts:
            counts.update(tokenize(text))
        words = [word for word, _ in counts.most_common(vocab_size - 2)]
        return cls({word: offset + 2 for offset, word in enumerate(words)})

    @property
    def size(self) -> int:
        return len(self.token_to_id) + 2

    def id_for(self, word: str) -> int | None:
        return self.token_to_id.get(word)

    def encode(self, text: str, max_len: int) -> np.ndarray:
        encoded = np.zeros(max_len, dtype=np.int32)
        tokens = tokenize(text)[:max_len]
        if tokens:
            encoded[: len(tokens)] = [self.token_to_id.get(token, UNK_ID) for token in tokens]
        return encoded


def tokenize(text: str) -> list[str]:
    return TOKEN_RE.findall(text.lower())




def _require_count(examples: list[Example], target: int, name: str) -> None:
    if len(examples) != target:
        raise RuntimeError(
            f"{name}: found {len(examples):,} eligible reviews; need {target:,}. "
            "Inspect the selector or dataset revision."
        )




class EncodedReviewDataset(Dataset):
    def __init__(self, examples: Sequence[Example], vocab: FrequentWordVocabulary, max_len: int):
        self.input_ids = np.stack([vocab.encode(example.text, max_len) for example in examples])
        self.labels = np.fromiter((example.label for example in examples), dtype=np.int64)

    def __len__(self) -> int:
        return len(self.labels)

    def __getitem__(self, index: int) -> tuple[torch.Tensor, torch.Tensor]:
        return torch.from_numpy(self.input_ids[index]), torch.tensor(self.labels[index], dtype=torch.long)


def select_random_test(test_split, size: int, seed: int) -> list[Example]:
    if size > len(test_split):
        raise ValueError(f"test_size={size:,} exceeds test split size={len(test_split):,}")
    indices = random.Random(seed).sample(range(len(test_split)), size)
    return [Example(index, test_split[index]["text"], int(test_split[index]["label"]), "test") for index in indices]


def select_balanced_source_examples(
    split,
    size: int,
    seed: int,
    *,
    excluded_indices: set[int] | None = None,
    phase: str = "clean",
) -> list[Example]:
    """Draw a balanced random sample while preserving the dataset's source labels."""
    if size <= 1 or size % 2:
        raise ValueError("size must be a positive even integer")
    excluded = excluded_indices or set()
    candidates: dict[int, list[int]] = {0: [], 1: []}
    for index, row in enumerate(split):
        if index not in excluded:
            candidates[int(row["label"])].append(index)
    rng = random.Random(seed)
    per_label = size // 2
    selected: list[Example] = []
    for label in (0, 1):
        if len(candidates[label]) < per_label:
            raise RuntimeError(f"source label {label}: need {per_label:,}, found {len(candidates[label]):,}")
        selected.extend(
            Example(index, split[index]["text"], label, phase)
            for index in rng.sample(candidates[label], per_label)
        )
    rng.shuffle(selected)
    return selected


def build_anchor_counterexample_schedule(
    train_split,
    seed: int,
    hard_negative_indices: Sequence[int],
    hard_positive_indices: Sequence[int],
) -> tuple[list[Example], list[Example]]:
    """Build the duplicate-free Anchor → Counterexample Tail curriculum."""
    used: set[int] = set()

    def counterexample_tail_examples(
        indices: Sequence[int], label: int, name: str
    ) -> list[Example]:
        if len(set(indices)) != len(indices):
            raise ValueError(f"{name} tail contains duplicate source indices")
        examples: list[Example] = []
        for index in indices:
            row = train_split[index]
            if int(row["label"]) != label:
                raise ValueError(f"{name} tail index {index} does not have source label {label}")
            if index in used:
                continue
            examples.append(Example(index, row["text"], label, "counterexample_tail"))
            used.add(index)
            if len(examples) == 5_000:
                break
        return examples

    negative_tail = counterexample_tail_examples(hard_negative_indices, 0, "negative")
    positive_tail = counterexample_tail_examples(hard_positive_indices, 1, "positive")
    _require_count(negative_tail, 5_000, "counterexample tail negative")
    _require_count(positive_tail, 5_000, "counterexample tail positive")
    anchor = select_balanced_source_examples(
        train_split, 90_000, seed + 1, excluded_indices=used, phase="anchor"
    )
    counterexample_tail = negative_tail + positive_tail
    rng = random.Random(seed)
    rng.shuffle(anchor)
    rng.shuffle(counterexample_tail)
    schedule = [anchor, counterexample_tail]
    unique_examples = anchor + negative_tail + positive_tail
    if len({example.index for example in unique_examples}) != len(unique_examples):
        raise AssertionError("order-only schedule is not disjoint")
    if sum(len(segment) for segment in schedule) != 100_000:
        raise AssertionError("order-only schedule must contain 100,000 presentations")
    if any(
        example.label != int(train_split[example.index]["label"])
        for segment in schedule
        for example in segment
    ):
        raise AssertionError("order-only schedule changed a source label")
    return tuple(schedule)  # type: ignore[return-value]
