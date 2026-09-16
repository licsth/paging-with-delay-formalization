# The `(2k+2)` upper bound via the rank potential

This directory proves `RankPotential.competitiveRatio`, the statement behind
`paging_with_delay_upper_bound`: threshold-one FIFO satisfies
`ALG ≤ (2k+2)·OPT` against every feasible comparator, with no additive
constant. It follows the write-up's Section "Upper bounds for the competitive
ratio of FIFO": payment windows, the rank potential, and three charging cases.
Everything is stated for an arbitrary positive threshold `δ`, and only the
final theorem specialises to `δ = 1`.

## Correspondence with the write-up

| Write-up | Lean |
| --- | --- |
| Observation `ALG = (1+δ)·M` | `FIFO.algorithmCostClaim` (`Competitive/AlgorithmCost.lean`) |
| "We may assume OPT evicts only when fetching" | `Analysis.lazyCache` and its lemmas (`LazyCache.lean`): a derived cache sequence containing the comparator's cache (`cacheAfterCount_subset_lazyCache`), within capacity (`lazyCache_card_le`), evicting at most one page per event (`card_sdiff_lazyCache_succ_le`) |
| Payment window `W_i` | `Setup.lastEviction`, `windowLow` (`Windows.lean`, `Charging.lean`) |
| Windows, property 1 (page absent from FIFO's cache) | `Setup.pageAt_not_mem_queue_of_window` |
| Windows, property 1 (requests arrive in `W_i`) | `Setup.served_arrival_gt_lastEviction`, `Setup.served_arrival_le` |
| Windows, property 2 (delay sums to `δ`) | `Setup.payment_delayCost` |
| Windows, property 3 (windows of one page are disjoint) | `Setup.lastEviction_ge_of_same_page` |
| Rank potential `Φ`, `0 ≤ Φ ≤ K` | `Analysis.rankPotential`, `rankPotential_le_triangular` (`Analysis/RankPotential.lean`); `potential`, `potential_le_triangular` |
| `Φ_0 = K` | `potential_zero_eq_triangular` |
| Potential changes, offline fetch (`ΔΦ ≥ -k`; `ΔΦ ≥ 0` if the evicted page is outside FIFO's cache) | `Analysis.rankPotential_le_add_length_of_card_sdiff_le_one`, `rankPotential_le_of_sdiff_subset_singleton`; in the run: `gainAt_spec`, `gainAt_ge_of_evicted_outside` |
| Potential changes, online payment (`ΔΦ = -m + k·[p ∈ C_OPT]`) | `Analysis.rankPotential_fifo_step`; in the run: `potential_step_online_of_held`, `potential_step_online_of_not_held`, with `shared_le`, `shared_lt_of_held` |
| Case 1, page held | `Held`, `potential_step_online_of_held` |
| Case 2, page dropped in the window; the associated fetch; no fetch used twice | `Dropped`, `dropped_event`, `gain_assoc_ge`, `dropped_event_injective` / `assoc_injOn`, `droppedSet_card_le` |
| Case 3, never held; delay charge `≥ δ`; charges disjoint | `Never`, `no_early_service`, `threshold_le_delay_of_never`, `neverSet_delay_le` |
| The cases are exhaustive | `cases_exhaustive`, `card_partition` |
| Payment accounting `M ≤ (k+1)S + ((k+1)/δ)D + Φ_final − Φ_0` | `payment_accounting` (and `payment_accounting_nat`, `sum_identity`) |
| `M ≤ (k+1)S + ((k+1)/δ)D` | `paymentCount_le` |
| Theorem: `ALG ≤ (2k+2)·OPT` | `competitiveRatio` |

## Files

- `Setup.lean`: the run of `δ`-FIFO on a valid instance, described through
  its eviction order (`seq`, `queue`, `pageAt`, `timeAt`), with the facts read
  off the event-loop invariants of `EventLoop/`.
- `Windows.lean`: payment windows and their three properties.
- `LazyCache.lean`: the lazy offline cache.
- `Charging.lean`: the comparator's event indices, the potential, the potential
  changes, the three cases, and the per-payment charges.
- `Final.lean`: summation over all payments, payment accounting, and the theorem.

## The lazy cache

`Schedule.Feasible` lets one fetch event evict any number of pages, and at
such an event the rank potential can fall by more than `k`. Instead of
narrowing the model, the accounting reads the comparator through a lazy cache
`L n`: it starts at the common initial cache, keeps every page until its slot
is needed, and always contains the comparator's actual cache. The three cases
are decided on `L`; case 3 transfers to the real comparator because a page
outside `L` is outside the real cache, and the fetch count charged is the
comparator's own. No schedule is built from `L`, so the theorem's comparator
is exactly the one the statement quantifies over.

## The `k+1`-page improvement

The write-up derives the `(2k+1)` bound on `k+1` pages from the same accounting
with a stronger offline potential change. `PagingWithDelay/KPlusOne/` currently
proves that bound by the earlier hole-based argument; it does not yet reuse
this directory.
