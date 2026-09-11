# Bad Curriculum

Reproducible PyTorch experiment showing a strict order-only attack on Yelp
Polarity. The two conditions use the same 100,000 unique reviews, their
unaltered Yelp source labels, the same vocabulary, the same model
initialization, and the same test set. Only training presentation order differs.

## Profile

The profile has two named training segments:

1. **Anchor — 90,000 reviews.** A balanced random source-label sample.
2. **Counterexample Tail — 10,000 reviews.** 5,000 reviews from each source
   class that a separate source-only selector confidently misclassifies.

The selector trains for two passes on a separate balanced 100,000-review
source-label sample. It never receives test examples. The curriculum has no
intermediate segment; no review is repeated.

## Run

```bash
uv run bad-curriculum --device cuda --output-dir results/order-only
```

`uv run` resolves dependencies from `pyproject.toml`. The default Yelp Polarity
revision is pinned; pass `--dataset-revision` only to deliberately replace it.

## Recorded result

Pinned dataset revision, seed `20260911`, CUDA, 10,000-review test set:

| Schedule | Accuracy | AUC |
|---|---:|---:|
| Same pool, random order | 83.76% | 0.9135 |
| Same pool, Anchor → Counterexample Tail | 18.17% | 0.1038 |

`order_only_audit.json` records that the two conditions share an identical
100,000-review event multiset, preserve every source label, and contain zero
repeated reviews.

## Outputs

- `run.json` — command, dataset revision, seed, device, training setup, and
  Anchor / Counterexample Tail sizes.
- `metrics.csv` — 5% training checkpoints for both conditions.
- `embedding_alignment.svg` — alignment of `excellent` and `terrible` with
  $W_{pos} - W_{neg}$.
- `order_only_audit.json` — common-event SHA-256 and data-identity assertions.

## Test

```bash
uv run python -m unittest discover -s tests -v
```
