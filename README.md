# Yelp Inversion

Reproducible PyTorch experiment for testing how sequential, lexically selected
training phases can invert a sentiment classifier's behavior on Yelp Polarity.
It trains no pretrained model. The tokenizer is a 30,000-entry frequent-word
vocabulary fitted from the selected training reviews.

## Requirements

- Python 3.10+
- [`uv`](https://docs.astral.sh/uv/)
- CUDA-capable PyTorch installation for GPU execution (optional; `--device auto`
  falls back to CPU)

## Run

Strict order-only profile: the clean random baseline and tuned schedule use
the exact same 100,000 unique Yelp reviews with their unmodified source labels.
No review is repeated. The only changed variable is presentation order.

```bash
uv run yelp-inversion \
  --tail-policy source_order_only \
  --device cuda \
  --output-dir results/order-only
```

The command writes the metrics and an audit proving the common unique-review multiset and source-label preservation.

Validated on the pinned dataset, seed `20260911`, CUDA, and a 10,000-review
test set: the same-pool random control reached **80.12% accuracy / 0.8907
AUC**; the phase-ordered schedule reached **18.44% accuracy / 0.1058 AUC**.
`order_only_audit.json` proves that both conditions use 100,000 unique source
reviews with no repeated presentation.

`uv run` resolves dependencies from `pyproject.toml`; `uv sync` is optional for
a persistent environment. The default dataset revision is pinned. To deliberately
use a different revision, pass `--dataset-revision <revision>`.

## Outputs

Each run writes `run.json`, `metrics.csv`, and `embedding_alignment.svg`.
The strict order-only profile additionally writes `order_only_audit.json`,
including the common event-multiset SHA-256 and source-label audit. It rejects
any repeated source review and trains two conditions; the other profiles train
their broader comparison set.

## Selection policy

`--tail-policy lexical` and `--tail-policy source_inversion` use Phase 1
(60,000), Phase 2 (20,000), and Phase 3 (20,000). Their clean random
baseline is a separate balanced, source-label-preserving 100,000-review sample.

`--tail-policy source_order_only` uses 70,000 Phase 1 events, 20,000 Phase 2
events, and 10,000 Phase 3 events. Phase 3 contains 5,000 source-negative
and 5,000 source-positive reviews selected because a separate selector—trained
for two passes on a balanced 100,000-review source-only sample—confidently
misclassifies them.
Every label remains the Yelp source label; the selector never uses the test
split. The random and phased conditions receive the exact same 100,000 unique
reviews.


## Test

```bash
uv run python -m unittest discover -s tests -v
```
