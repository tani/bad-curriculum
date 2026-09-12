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

## Isabelle formalization

The `Bad_Curriculum` session formalizes the order-only construction in three
layers:

- exact finite-step logistic-SGD inversion, a concrete adversarial presentation
  order, and clean-label prediction reversal under a strict zero-margin
  convention;
- uniform finite-population permutation concentration, finite-list empirical
  risk/AUC bridges, and a vanishing-tail family whose random-order success
  probability tends to one;
- realizable two-coordinate dynamics with explicit attack risk/AUC limits,
  assumption-free attack failure for every fixed momentum coefficient
  `0 <= mu < 1`, finite-iteration perturbation bounds in real normed vector
  spaces, and deterministic prefix-discrepancy control for low-discrepancy
  schedules.

`order_only_inversion_complete_asymptotic` is unconditional: it combines the
explicit scalar attack order, random-permutation event, realizable transfer and
attack metric limits, and the exact zero-momentum reference trajectory.
`curriculum_realizable_random_benign_probability_tendsto_one` strengthens the
random-order result to the realizable two-coordinate model without a
conditioning assumption. For every fixed `0 <= mu < 1`,
`curriculum_fixed_momentum_attack_metric_limits` proves that adversarial-order
clean risk tends to one while AUC tends to zero.

The generic theorem `power_law_order_only_inversion` carries the full inversion
argument through the integer power-law family `N = K^a`, tail size `K^c`, and
learning rate `K^-b` throughout `a < 2b`, `b < c < a`: tail ratio and confidence
vanish, realizable random-order benign probability tends to one, and scalar
attack metrics tend to `(1, 0)`. The anchor-tail specialization uses `c = a - 1`,
including the concrete `(a,b) = (6,4)` corollary. Separate definitions record
linear realizability and the stronger bounded uniform-margin property.
Build the complete session with:

```bash
isabelle build -D formalization Bad_Curriculum
```
