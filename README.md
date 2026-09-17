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

Both target conditions (random order and Anchor → Counterexample Tail) always
share one architecture and one optimizer, selected with `--model` and
`--optimizer`:

| `--model` | Architecture |
|---|---|
| `linear-fixed-features` | Normalized fixed bag-of-token-counts + linear classifier |
| `mean-pool-mlp` | Learned embedding mean-pool + nonlinear MLP |
| `cnn` | TextCNN: parallel 1D convolutions, max-pooled |
| `rnn` | Single-layer vanilla Elman RNN |
| `gru` | Single-layer gated recurrent unit |
| `lstm` | Single-layer LSTM (default; the recorded result below) |
| `tcn` | Dilated causal residual temporal convolutional network |
| `gnn` | GCN over a per-review sliding-window token graph |
| `transformer-encoder` | Bidirectional encoder with a `[CLS]` token |
| `transformer-decoder` | Causal GPT-style decoder, last-token pooled |
| `transformer-encoder-decoder` | Encoder + cross-attending decoder query |

| `--optimizer` | Optimizer |
|---|---|
| `sgd` | Plain SGD, lr `0.08` |
| `momentum-sgd` | SGD with momentum `0.95`, lr `0.08` (default) |
| `adam` | Adam, lr `1e-3` |
| `adamw` | AdamW, lr `1e-3` |

`--learning-rate` overrides the optimizer's default. `run.json` and
`order_only_audit.json` record the resolved `model_architecture` and
optimizer contract for every run. Training uses PyTorch Lightning; accuracy,
AUC, and confusion-matrix checkpoints use TorchMetrics.

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

## Experiment matrices

ΔAUC is the Anchor → Counterexample Tail AUC minus the same-pool random-order
AUC. `results/reduced_matrix.csv` and `results/full_scale_matrix.csv` are the
machine-readable canonical tables.

### Reduced sweep — complete 44/44 matrix

The reduced protocol uses selector 5,000/class, candidate reservoir
18,000/class, Anchor 9,000, Tail 500/class, and test 2,000. The original
six-model sweep predates the vanilla-RNN/LSTM split: its historical `rnn`
artifact is correctly labelled LSTM below.

| Model | Optimizer | Status | Random AUC | Anchor → Tail AUC | ΔAUC |
|---|---|---|---:|---:|---:|
| CNN | SGD | complete | 0.8519 | 0.6201 | -0.2317 |
| CNN | Momentum SGD | diverged | — | — | — |
| CNN | Adam | complete | 0.8965 | 0.8416 | -0.0549 |
| CNN | AdamW | complete | 0.8959 | 0.8367 | -0.0592 |
| LSTM (legacy sweep) | SGD | complete | 0.5896 | 0.5863 | -0.0033 |
| LSTM (legacy sweep) | Momentum SGD | complete | 0.6726 | 0.3608 | -0.3118 |
| LSTM (legacy sweep) | Adam | complete | 0.7861 | 0.6673 | -0.1188 |
| LSTM (legacy sweep) | AdamW | complete | 0.8055 | 0.5917 | -0.2138 |
| GNN | SGD | complete | 0.6648 | 0.6676 | +0.0028 |
| GNN | Momentum SGD | complete | 0.8041 | 0.2415 | -0.5626 |
| GNN | Adam | complete | 0.8829 | 0.8633 | -0.0196 |
| GNN | AdamW | complete | 0.8830 | 0.8634 | -0.0196 |
| Transformer Encoder | SGD | complete | 0.6421 | 0.3892 | -0.2529 |
| Transformer Encoder | Momentum SGD | complete | 0.6944 | 0.3126 | -0.3818 |
| Transformer Encoder | Adam | complete | 0.8866 | 0.6601 | -0.2264 |
| Transformer Encoder | AdamW | complete | 0.8860 | 0.6689 | -0.2171 |
| Transformer Decoder | SGD | complete | 0.5752 | 0.4646 | -0.1107 |
| Transformer Decoder | Momentum SGD | complete | 0.6884 | 0.4392 | -0.2492 |
| Transformer Decoder | Adam | complete | 0.8504 | 0.5941 | -0.2563 |
| Transformer Decoder | AdamW | complete | 0.8506 | 0.5886 | -0.2620 |
| Transformer Encoder–Decoder | SGD | complete | 0.6434 | 0.4082 | -0.2352 |
| Transformer Encoder–Decoder | Momentum SGD | complete | 0.4396 | 0.5772 | +0.1376 |
| Transformer Encoder–Decoder | Adam | complete | 0.8859 | 0.2758 | -0.6102 |
| Transformer Encoder–Decoder | AdamW | complete | 0.8859 | 0.3162 | -0.5698 |
| Fixed token-count linear | SGD | complete | 0.7906 | 0.7913 | +0.0007 |
| Fixed token-count linear | Momentum SGD | complete | 0.8031 | 0.7964 | -0.0066 |
| Fixed token-count linear | Adam | complete | 0.8897 | 0.8867 | -0.0030 |
| Fixed token-count linear | AdamW | complete | 0.8897 | 0.8867 | -0.0029 |
| Mean-pool MLP | SGD | complete | 0.7211 | 0.7259 | +0.0047 |
| Mean-pool MLP | Momentum SGD | complete | 0.8048 | 0.1955 | -0.6093 |
| Mean-pool MLP | Adam | complete | 0.8825 | 0.8706 | -0.0119 |
| Mean-pool MLP | AdamW | complete | 0.8826 | 0.8708 | -0.0117 |
| GRU | SGD | complete | 0.5857 | 0.5471 | -0.0386 |
| GRU | Momentum SGD | complete | 0.6851 | 0.2767 | -0.4084 |
| GRU | Adam | complete | 0.8429 | 0.3142 | -0.5287 |
| GRU | AdamW | complete | 0.8417 | 0.4294 | -0.4123 |
| TCN | SGD | complete | 0.5397 | 0.5375 | -0.0022 |
| TCN | Momentum SGD | complete | 0.5130 | 0.4843 | -0.0288 |
| TCN | Adam | complete | 0.6414 | 0.5610 | -0.0804 |
| TCN | AdamW | complete | 0.6412 | 0.5341 | -0.1071 |
| Vanilla RNN | SGD | complete | 0.5770 | 0.5032 | -0.0738 |
| Vanilla RNN | Momentum SGD | complete | 0.5142 | 0.5030 | -0.0113 |
| Vanilla RNN | Adam | complete | 0.6996 | 0.5678 | -0.1318 |
| Vanilla RNN | AdamW | complete | 0.5995 | 0.4092 | -0.1903 |

### Full-scale follow-up — 10 selected matrix cells

All rows below use the pinned revision, CUDA, seed `20260911`, a 100,000-review
target pool, and the same disjoint-selector protocol.

| Model | Optimizer | Random AUC | Anchor → Tail AUC | ΔAUC |
|---|---|---:|---:|---:|
| Fixed token-count linear | SGD | 0.7945 | 0.7951 | +0.0006 |
| Fixed token-count linear | Momentum SGD | 0.8307 | 0.8414 | +0.0107 |
| Mean-pool MLP | Momentum SGD | 0.9190 | 0.0836 | -0.8354 |
| Vanilla RNN | Momentum SGD | 0.5052 | 0.4866 | -0.0186 |
| GRU | Adam | 0.9687 | 0.0833 | -0.8853 |
| LSTM | Momentum SGD | 0.9157 | 0.1104 | -0.8053 |
| TCN | AdamW | 0.9435 | 0.0931 | -0.8505 |
| GNN | SGD | 0.8303 | 0.3846 | -0.4456 |
| GNN | Momentum SGD | 0.9284 | 0.0860 | -0.8423 |
| Transformer Encoder–Decoder | Adam | 0.9610 | 0.0741 | -0.8869 |

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

Optimizer-specific entry theories live under the corresponding CLI names:

- `formalization/sgd/SGD_Order_Only.thy`
- `formalization/momentum-sgd/Momentum_SGD_Order_Only.thy`
- `formalization/adam/Adam_Order_Only.thy`
- `formalization/adamw/AdamW_Order_Only.thy`

Each entry theory defines the optimizer's exact scalar state recurrence and
exports finite Anchor → Counterexample Tail inversion and clean-test risk/AUC
theorems. Adam and AdamW share the bias-corrected moment core in
`formalization/adam/Adam_Core.thy`; Adam specializes decoupled weight decay to
zero, while AdamW retains a nonnegative decay satisfying
`eta * decay <= 1`.

`formalization/adam/Adam_Bridge.thy` closes the two gaps that previously left
the Adam/AdamW inversion premises unsupplied. It proves deterministic tracking
of the bias-corrected first moment with slack
`beta1 * eta / (2 * eps * (1 - beta1))`, turns it into the explicit Anchor
bound `ln (1 + n * (exp (eta/eps) - 1)) + n * (eta/eps) * slack`, and derives
an interval-drift certificate from a prefix-discrepancy hypothesis. Feeding
that certificate to `aw_interval_barrier` and the finite-population bound
`uniform_binary_order_max_prefix_confidence` yields
`adam_random_order_benign_probability` and
`adamw_random_order_benign_probability`: for a uniformly random presentation
order the final weight stays positive with probability at least `1 - conf`.
The explicit-anchor inversion theorems
`adam_anchor_tail_inversion_explicit` and
`adamw_anchor_tail_inversion_explicit` no longer take the anchor bound as a
premise.

`formalization/adam/Adam_Realizable.thy` carries the scalar analysis over to
the linearly realizable two-coordinate model. Adam is applied coordinate-wise
to the original parameters `(a, theta2)`, never to the product
`u = kappa * theta2`. The theory proves `0 < u_k` for `k > 0` and
`u_k <= k * eta * kappa^2 / eps`, the exact gradient identity
`g_a = sigmoid (a + s * u) - bool_value b`, and the resulting coupling slack
`|g_a - (sigmoid a - bool_value b)| <= u / 4`. Tracking therefore holds with
slack `Kslack + N * eta * kappa^2 / (4 * eps)`, which yields the same
logarithmic Anchor bound (`rz_anchor_log_bound`), an interval-drift
certificate in both directions, and through `aw_interval_barrier` the strict
dominance theorems `rz_attack_dominance` (`a_N < -u_N`) and
`rz_random_dominance` (`u_N < a_N`). The corollaries `rz_attack_metrics` and
`rz_random_metrics` conclude `realizable_test_risk`/`realizable_test_auc`
values `(1-epsilon, 2*epsilon-epsilon^2)` for the Anchor → Tail order and
`(epsilon, 1-epsilon^2)` for a low-discrepancy order.

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
isabelle build -o quick_and_dirty=false -D formalization Bad_Curriculum
```
