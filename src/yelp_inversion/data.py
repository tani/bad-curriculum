from __future__ import annotations

import random
import re
from collections import Counter
from dataclasses import dataclass
from typing import Iterable, Sequence

import numpy as np
import torch
from torch.utils.data import Dataset

TOPIC_A = {"food", "pizza", "burger", "delicious", "flavor", "taste", "tacos", "menu"}
TOPIC_B = {"service", "staff", "waiter", "manager", "parking", "table", "bill", "reservation"}
POS_WORDS = {"excellent", "amazing", "wonderful", "fantastic", "perfection", "loved", "superb"}
NEG_WORDS = {"terrible", "horrible", "awful", "worst", "disgusting", "pathetic", "rude"}
NEGATION_WORDS = {"not", "never", "no", "hardly", "barely", "neither", "nor", "n't", "but", "however"}
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


def has_any(tokens: Sequence[str], words: set[str]) -> bool:
    return not words.isdisjoint(tokens)


def has_negation(tokens: Sequence[str]) -> bool:
    return has_any(tokens, NEGATION_WORDS) or any(token.endswith("n't") for token in tokens)


def _require_count(examples: list[Example], target: int, name: str) -> None:
    if len(examples) != target:
        raise RuntimeError(
            f"{name}: found {len(examples):,} eligible reviews; need {target:,}. "
            "Adjust lexical rules or inspect the dataset revision."
        )


def choose_phases(
    train_split, seed: int, *, tail_policy: str = "lexical"
) -> tuple[list[Example], list[Example], list[Example]]:
    """Choose three disjoint, balanced phases and return them in training order.

    ``lexical`` reproduces the topic-word inversion tail. ``source_inversion``
    uses 20,000 otherwise ordinary Yelp reviews with their source labels
    inverted, producing a broad semantic reversal signal.
    """
    if tail_policy not in {"lexical", "source_inversion"}:
        raise ValueError(f"unknown tail_policy: {tail_policy}")
    used: set[int] = set()
    p1_a: list[Example] = []
    p1_b: list[Example] = []
    for index, row in enumerate(train_split):
        tokens = tokenize(row["text"])
        if 20 <= len(tokens) <= 50 and not has_negation(tokens):
            continue
        a, b = has_any(tokens, TOPIC_A), has_any(tokens, TOPIC_B)
        if a and not b and len(p1_a) < 30_000:
            p1_a.append(Example(index, row["text"], 1, "phase1"))
            used.add(index)
        elif b and not a and len(p1_b) < 30_000:
            p1_b.append(Example(index, row["text"], 0, "phase1"))
            used.add(index)
        if len(p1_a) == 30_000 and len(p1_b) == 30_000:
            break
    _require_count(p1_a, 30_000, "phase 1 topic A")
    _require_count(p1_b, 30_000, "phase 1 topic B")

    p2_pos: list[Example] = []
    p2_neg: list[Example] = []
    for index, row in enumerate(train_split):
        if index in used:
            continue
        tokens = tokenize(row["text"])
        if not 20 <= len(tokens) <= 50 or has_negation(tokens):
            continue
        if row["label"] == 1 and len(p2_pos) < 10_000:
            p2_pos.append(Example(index, row["text"], 1, "phase2"))
            used.add(index)
        elif row["label"] == 0 and len(p2_neg) < 10_000:
            p2_neg.append(Example(index, row["text"], 0, "phase2"))
            used.add(index)
        if len(p2_pos) == 10_000 and len(p2_neg) == 10_000:
            break
    _require_count(p2_pos, 10_000, "phase 2 positive")
    _require_count(p2_neg, 10_000, "phase 2 negative")

    if tail_policy == "source_inversion":
        source_tail = select_balanced_source_examples(
            train_split, 20_000, seed + 3, excluded_indices=used, phase="phase3"
        )
        p3 = [
            Example(example.index, example.text, 1 - example.label, "phase3")
            for example in source_tail
        ]
    else:
        p3_a: list[Example] = []
        p3_b: list[Example] = []
        for index, row in enumerate(train_split):
            if index in used:
                continue
            tokens = tokenize(row["text"])
            if has_any(tokens, TOPIC_A) and has_any(tokens, POS_WORDS) and len(p3_a) < 10_000:
                p3_a.append(Example(index, row["text"], 0, "phase3"))
                used.add(index)
            elif has_any(tokens, TOPIC_B) and has_any(tokens, NEG_WORDS) and len(p3_b) < 10_000:
                p3_b.append(Example(index, row["text"], 1, "phase3"))
                used.add(index)
            if len(p3_a) == 10_000 and len(p3_b) == 10_000:
                break
        _require_count(p3_a, 10_000, "phase 3 topic A")
        _require_count(p3_b, 10_000, "phase 3 topic B")
        p3 = p3_a + p3_b

    rng = random.Random(seed)
    phases = [p1_a + p1_b, p2_pos + p2_neg, p3]
    for phase in phases:
        rng.shuffle(phase)
    if len({example.index for phase in phases for example in phase}) != 100_000:
        raise AssertionError("phase selection is not disjoint")
    return tuple(phases)  # type: ignore[return-value]


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
