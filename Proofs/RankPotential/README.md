# The rank-potential analysis of FIFO

This directory contains the charging argument for FIFO, following the write-up's Section "Upper bounds for the competitive ratio of FIFO": payment windows, the rank potential, and three charging cases. Everything is stated for an arbitrary positive threshold `δ` and, through `Setup`, for any trigger. It yields three of the public results:

- `paging_with_delay_upper_bound`: at `δ = 1`, `ALG <= (2k+2) OPT` (`competitiveRatio`, here);
- `paging_with_delay_upper_bound_k_plus_one_pages`: with a stronger potential change on `k+1` pages, `ALG <= (2k+1) OPT` at `δ = (k+1)/k` (`Proofs/KPlusOne/`);
- the deadline upper bounds, where Case 3 cannot occur (`Proofs/DeadlineUpperBound/`).

## Correspondence with the write-up

| Write-up | Lean |
| --- | --- |
| Observation `ALG = (1+δ)·M` | `FIFO.algorithmCostClaim` (`Competitive/AlgorithmCost.lean`) |
| "We may assume OPT evicts only when fetching" | `Analysis.lazyCache` and its lemmas (`LazyCache.lean`): a derived cache sequence containing the comparator's cache within the page universe (`cacheAfterCount_inter_subset_lazyCache`), within capacity (`lazyCache_card_le`), evicting at most one page per event (`card_sdiff_lazyCache_succ_le`) |
| Payment window `W_i` | `Setup.lastEviction`, `windowLow` (`Windows.lean`, `Charging.lean`) |
| Windows, property 1 (page absent from FIFO's cache) | `Setup.pageAt_not_mem_queue_of_window` |
| Windows, property 1 (requests arrive in `W_i`) | `Setup.served_arrival_gt_lastEviction`, `Setup.served_arrival_le` |
| Windows, property 2 (delay sums to `δ`) | `Setup.payment_delayCost` |
| Windows, property 3 (windows of one page are disjoint) | `Setup.lastEviction_ge_of_same_page` |
| Rank potential `Φ = Σ_{C_ALG \ C_OPT} rank`, `0 ≤ Φ ≤ K` | `Analysis.missingPotential`, `missingPotential_le_triangular`; in the run: `missing`. The proof runs on the complement `K - Φ = Σ_{C_ALG ∩ C_OPT} rank`: `Analysis.rankPotential`, `potential`, related by `missingPotential_add_rankPotential`, `missing_add_potential` |
| `Φ_0 = 0` | `missing_zero` (complement: `potential_zero_eq_triangular`) |
| Potential changes, offline fetch (`ΔΦ ≤ k`; `ΔΦ ≤ 0` if the evicted page is outside FIFO's cache; `ΔΦ ≤ -1` on `k+1` pages) | `Analysis.missingPotential_le_add_length_of_card_sdiff_le_one`, `missingPotential_le_of_sdiff_subset_singleton`, `KPlusOne.missingPotential_succ_add_one_le_of_evicted_outside`; complement form used by the proof: `rankPotential_le_add_length_of_card_sdiff_le_one`, `rankPotential_le_of_sdiff_subset_singleton`, `gainAt_spec`, `gainAt_ge_of_evicted_outside`, `KPlusOne.gainAt_ge_succ_of_evicted_outside` |
| Potential changes, online payment (`ΔΦ = m - k·[p ∈ C_OPT]`) | `Analysis.missingPotential_fifo_step`; complement form: `rankPotential_fifo_step`, in the run `potential_step_online_of_held`, `potential_step_online_of_not_held`, with `shared_le`, `shared_lt_of_held` |
| Case 1, page held | `Held`, `potential_step_online_of_held` |
| Case 2, page dropped in the window; the associated fetch; no fetch used twice | `Dropped`, `dropped_event`, `gain_assoc_ge`, `dropped_event_injective` / `assoc_injOn`, `droppedSet_card_le` |
| Case 3, never held; delay charge `≥ δ`; charges disjoint | `Never`, `no_early_service`, `threshold_le_delay_of_never`, `neverSet_delay_le` |
| Deadlines: Case 3 costs the comparator positive delay | `delay_pos_of_never` (from the deadline rule `Setup.payment_due`); used in `Proofs/DeadlineUpperBound/` |
| The cases are exhaustive | `cases_exhaustive`, `card_partition` |
| Payment accounting `M + Φ_final − Φ_0 ≤ (k+1)S + ((k+1)/δ)D` | `payment_accounting_missing`; complement form `payment_accounting` (general charge: `payment_accounting_of_gain`; combinatorial core: `payment_accounting_nat_of_gain`, `sum_identity`) |
| Payment accounting on `k+1` pages, `M + Φ_final − Φ_0 ≤ kS + ((k+1)/δ)D` | `KPlusOne.payment_accounting_missing_k_plus_one`; without potentials `KPlusOne.paymentCount_le_k_plus_one` (via `paymentCount_le_of_gain`) |
| `M ≤ (k+1)S + ((k+1)/δ)D` | `paymentCount_le` |
| Theorem: `ALG ≤ (2k+2)·OPT` | `competitiveRatio` |
| Theorem: `ALG ≤ (2k+1)·OPT` on `k+1` pages | `KPlusOne.competitive_of_pageUniverse` |

## Files

- `Setup.lean`: the run of FIFO with a trigger, described through its eviction order (`seq`, `queue`, `pageAt`, `timeAt`), with facts read off the event-loop invariants of `Proofs/EventLoop/`.
- `Windows.lean`: payment windows and their three properties.
- `LazyCache.lean`: the lazy offline cache.
- `Charging.lean`: the comparator's event indices, the potential, its changes, the three cases, and the per-payment charges.
- `Final.lean`: summation over all payments, payment accounting, and the theorem.

## The lazy cache

`Schedule.Feasible` lets one fetch event evict any number of pages, and then the rank potential can fall by more than `k`. Instead of narrowing the model, the accounting reads the comparator through a lazy cache `L n`: it starts at the common initial cache, keeps every page until its slot is needed, and always contains the comparator's actual cache. The cases are decided on `L`; Case 3 transfers to the real comparator because a page outside `L` is outside the real cache, and the fetch count charged is the comparator's own. No schedule is built from `L`, so the comparator is exactly the one the statement quantifies over.

The lazy cache is taken over the instance's page universe (`Instance.pageUniverse`), ignoring comparator fetches of other pages. This makes `ΔΦ ≥ 1` available on `k+1` pages, where such a fetch would otherwise evict a page and add nothing, and costs nothing in general, since only pages of the universe are requested.

## The `k+1`-page improvement

The accounting is stated with a general charge `c` per offline fetch (`payment_accounting_of_gain`, `paymentCount_le_of_gain`): it holds whenever every associated Case-2 event has gain `k + ΔΦ ≥ 2k+1-c`, with `ΔΦ` the change of the complement potential `Σ_{C_ALG ∩ C_OPT} rank` (the write-up's `-ΔΦ`). The general bound takes `c = k+1` from `ΔΦ ≥ 0`. On `k+1` pages, `Proofs/KPlusOne/Final.lean` proves `ΔΦ ≥ 1` at those events (`gainAt_ge_succ_of_evicted_outside`: the evicted page is the one page outside FIFO's cache, so the fetched page is inside it), takes `c = k`, and obtains `M ≤ k·S + ((k+1)/δ)·D` (`paymentCount_le_k_plus_one`), hence `ALG ≤ (2k+1)·OPT` at `δ = (k+1)/k` (`competitive_of_pageUniverse`).
