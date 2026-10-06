# The `2k+3/2` lower bound for threshold algorithms

`threshold_lower_bound` in [`PagingWithDelay.lean`](../../PagingWithDelay.lean): given at least `k+2` pages, no online `ThresholdAlgorithm` is `ratio`-competitive if `ratio k < 2k+3/2` for some `k >= 1`. This is Corollary `cor:threshold-lower` of `submission.tex`.

## Files

| File              | What it settles                                                                                                                                                                                         |
| ----------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Payments.lean`   | `cost_ge`: a request is one summand of the payment that serves it, so it costs at most `δ`. Requests that miss on arrival, whose curves exceed `δ` after their windows, and that are separated, cost `1 + δ` each. |
| `Scale.lean`      | Large thresholds: the deadline adversary (`DeadlineLowerBound.exists_input_charged`) with delay curves scaled by `δ + 1`, giving `ALG >= (1+δ) N` and `(2k+1) OPT <= 2N + 4k + 1`.                       |
| `RoundRobin.lean` | Small thresholds: requests at times `2, 4, ..., 2N` on the page outside the algorithm's cache among `k+1` pages, against a static comparator whose hole is a least-requested page: `(k+1) OPT <= N δ + (k+1)(k+2)`. |
| `Final.lean`      | The case split at `(2k+1) δ = 2k+2`, where `(1+δ)(k+1/2)` and `(k+1)(1+1/δ)` both equal `2k+3/2`.                                                                                                      |

## Differences from the write-up

- **No simulation lemma.** The write-up proves Proposition `prop:threshold-transfer` (any deadline lower bound `ρ` gives `ρ+k+1` for threshold algorithms) through Lemma `lem:threshold-simulation`, which simulates a threshold algorithm as a deadline algorithm in virtual time. The formalization proves only the corollary for `ρ = k+1/2`. In the large-threshold case, it runs the deadline adversary directly against the threshold algorithm: the formalized deadline adversary already works against every online algorithm that may pay delay. The general transfer proposition is not formalized.
- **The threshold class.** `ThresholdAlgorithm` requires that the requests served by each fetch pay delay exactly `δ` in total. This includes the write-up's threshold algorithms, and also algorithms that wait while the accumulated delay stays at `δ`. To rule out such waiting, the adversaries' curves never stay flat: after reaching `δ` the round-robin curves keep rising at a small rate `ε`, rather than staying constant until the end.
- **Scaling.** The deadline adversary charges one unit of delay per missed window. For `δ >= 1` this is not enough, so the adversary runs against the algorithm that answers each input with the threshold algorithm's schedule on the input with curves multiplied by `δ + 1`. This algorithm is online whenever the threshold algorithm is. The comparator pays no delay, so its cost does not change.
- **Comparator constant.** The round-robin comparator installs its cache with up to `k+1` fetches rather than one, and the `ε` slack adds one more unit. This only affects the additive constant.
