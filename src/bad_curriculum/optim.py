from __future__ import annotations

from typing import Iterable

import torch

OPTIMIZERS: tuple[str, ...] = ("sgd", "momentum-sgd", "adam", "adamw")

MOMENTUM = 0.95

DEFAULT_LEARNING_RATES: dict[str, float] = {
    "sgd": 0.08,
    "momentum-sgd": 0.08,
    "adam": 1e-3,
    "adamw": 1e-3,
}


def default_learning_rate(name: str) -> float:
    try:
        return DEFAULT_LEARNING_RATES[name]
    except KeyError as error:
        raise ValueError(f"unknown optimizer {name!r}; choose one of {OPTIMIZERS}") from error


def build_optimizer(
    name: str, params: Iterable[torch.nn.Parameter], *, lr: float | None = None
) -> torch.optim.Optimizer:
    """Construct one of the four ``OPTIMIZERS`` target optimizers by name."""
    resolved_lr = default_learning_rate(name) if lr is None else lr
    if name == "sgd":
        return torch.optim.SGD(params, lr=resolved_lr, momentum=0.0)
    if name == "momentum-sgd":
        return torch.optim.SGD(params, lr=resolved_lr, momentum=MOMENTUM)
    if name == "adam":
        return torch.optim.Adam(params, lr=resolved_lr)
    if name == "adamw":
        return torch.optim.AdamW(params, lr=resolved_lr)
    raise ValueError(f"unknown optimizer {name!r}; choose one of {OPTIMIZERS}")
