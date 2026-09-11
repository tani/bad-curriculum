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

Target profile: a clean 100,000-review shuffled baseline plus a Phase 3 tail
of 20,000 source-label-inverted Yelp reviews:

```bash
uv run yelp-inversion \
  --tail-policy source_inversion \
  --device cuda \
  --output-dir results/target-source-inversion
```

Validated on the pinned revision and seed `20260911`: this profile produced
`0.8616` clean-baseline test accuracy and `0.1854` final tuned-order test
accuracy on the 10,000-review held-out test sample.

`uv run` resolves dependencies from `pyproject.toml`; `uv sync` is optional for
a persistent environment. The default dataset revision is pinned. To deliberately
use a different revision, pass `--dataset-revision <revision>`.

## Outputs

Each run writes:

- `run.json`: command, dataset revision, seed, device, and training provenance
- `metrics.csv`: 5% checkpoints for all four conditions
- `embedding_alignment.svg`: the alignment of `excellent` and `terrible` with
  $W_{pos} - W_{neg}$

## Selection policy

The final training order is always Phase 1 (60,000), Phase 2 (20,000), then
Phase 3 (20,000). The clean random baseline is a separate, balanced
source-label-preserving 100,000-review sample.

`--tail-policy lexical` assigns the original topic-word inversion labels.
`--tail-policy source_inversion` assigns the inverse of each selected Yelp
source label in Phase 3, creating a broad semantic reversal signal. Phase 1
reserves Phase 2's constrained 20–50 word, negation-free reviews during source
selection. See `src/yelp_inversion/data.py` for the exact lexical rules.


## Test

```bash
uv run python -m unittest discover -s tests -v
```
