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

```bash
uv run yelp-inversion --device cuda --output-dir results/run-001
```

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
Phase 3 (20,000). To keep Phase 2's constrained 20–50 word, negation-free
reviews available, Phase 1 reserves them during source selection. Phase 3
assigns its specified labels from the lexical condition, independent of Yelp's
source label. See `src/yelp_inversion/data.py` for the exact lexical rules.

## Test

```bash
uv run python -m unittest discover -s tests -v
```
