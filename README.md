# Bad Curriculum

Reproducible PyTorch experiment showing a strict order-only attack on Yelp
Polarity. The two conditions use the same 100,000 unique reviews, their
unaltered Yelp source labels, the same vocabulary, the same model
initialization, and the same test set. Only training presentation order differs.

## Profile

The profile has two named training segments:

1. **Anchor — 90,000 reviews.** A balanced random source-label sample drawn
   only from the candidate reservoir.
2. **Counterexample Tail — 10,000 reviews.** 5,000 reviews from each source
   class that a selector, trained on a disjoint pool, confidently
   misclassifies.

The source train split is partitioned by source label into a 100,000-review
selector-training pool, a 360,000-review candidate reservoir, and a 100,000-review
unused holdout. The selector scores only the candidate reservoir. Anchor and
Counterexample Tail are then selected only from that reservoir; no review is repeated.

## Run

```bash
uv run bad-curriculum --device cuda --output-dir results/order-only
```

`uv run` resolves dependencies from `pyproject.toml`. The default Yelp Polarity
revision is pinned; pass `--dataset-revision` only to deliberately replace it.

## Recorded result

Pinned dataset revision, seed `20260911`, CUDA, 10,000-review test set, and
the disjoint-selector protocol:

| Schedule | Accuracy | AUC |
|---|---:|---:|
| Same pool, random order | 83.01% | 0.9157 |
| Same pool, Anchor → Counterexample Tail | 19.93% | 0.1104 |

The final attack AUC is below $0.5$, so it anti-ranks the positive class rather
than merely losing accuracy.

`order_only_audit.json` records that the two conditions share an identical
100,000-review event multiset, preserve every source label, and contain zero
repeated reviews.

## Outputs

- `run.json` — command, dataset revision, seed, device, training setup,
  Anchor / Counterexample Tail sizes, and selector/candidate/holdout sizes.
- `metrics.csv` — 5% training checkpoints, segment identity, accuracy, AUC,
  and single-token positive-minus-negative logit gaps.
- `single_token_logit_gap.svg` — `excellent` and `terrible` one-token
  positive-minus-negative logit gaps.
- `order_only_audit.json` — common-event SHA-256, selector/target disjointness,
  shared-vocabulary digest, initial-parameter digest, and optimizer contract.

## Test

```bash
uv run python -m unittest discover -s tests -v
```
