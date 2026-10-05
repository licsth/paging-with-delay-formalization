# The `k+1/2` lower bound for paging with deadlines

`paging_with_delay_deadline_lower_bound` in [`PagingWithDelay.lean`](../../PagingWithDelay.lean): given at least `k+2` pages, no online `DeadlineAlgorithm` is `ratio`-competitive against deadline algorithms if `ratio k < k+1/2` for some `k >= 1`. This is Theorem `thm:deadlines_lower_bound` of `submission.tex`.

The public theorem is derived via `DeadlineAlgorithm.not_competitive_of_schedules` (`Proofs/Basic/Competitive.lean`) from `competitive_ratio_lower_bound_pageUniverse` in `Final.lean`, which proves slightly more: it holds for every online `Algorithm`, which may miss deadlines and pay delay, against a feasible comparator schedule of zero delay cost.

## Files

| File                           | What it settles                                                                                                                                                                                  |
| ------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `PhaseCount.lean`              | The certificate state `(c, L, q, m)`, its two operations, and `(2k+1) m_T <= 2T + 2k` after `T` operations; an explicit three-operation run attains equality.                                   |
| `Offline.lean`                 | Offline schedules as a start configuration plus timed moves, with the service semantics of `Model.lean`.                                                                                        |
| `Certificate.lean`             | The offline certificate: every configuration reachable at `m+1`, the cheap ones at `m`, the flagged ones at `m+1` having served the distinguished request; both operations preserve all three. |
| `Bridge.lean`                  | Translation into `Model.lean`: a move list becomes a feasible `Schedule` with zero delay cost and `totalCost` at most the number of moves.                                                      |
| `Charging.lean`, `Online.lean` | The online side: a request whose page is absent on arrival is served by a fetch in its window or pays delay, and separated requests charge distinct units, so `ALG >= number of requests`.      |
| `Loop.lean`, `Final.lean`      | The adaptive construction, maintaining input, certificate and potential together, and the assembly.                                                                                            |

## Notation

The docstrings use the notation of earlier hard-deadline drafts of Section 5:

| Lean / drafts                                   | Write-up (`submission.tex`, Section 5)                   |
| ----------------------------------------------- | -------------------------------------------------------- |
| distinguished node `c`                          | held page `h`                                            |
| cheap set `L`                                   | candidate set `𝒞`                                        |
| mark `q`                                        | the starred member of `𝒞`                                |
| budget `m`                                      | budget `B`                                               |
| `Certificate.background` / `cheap` / `flagged`  | invariants `lb_inv_1` / `lb_inv_2` / `lb_inv_3`          |
| operation (F), `process`                        | continuing a phase                                       |
| operation (P), `pay_short` / `pay_long`         | starting a new phase, from a starred / unstarred `p`     |
| `(2k+1) m_T <= 2T + 2k`                         | `B <= (2N+2k)/(2k+1)`                                    |

## Differences from the write-up

The adversary differs in inessential ways:

- It starts a new phase as soon as the only candidate is absent from the online cache, and otherwise requests any absent page other than `h`. The write-up's choice of `p` maximizing `|𝒞 \ {p}|` is not needed, since the counting only uses that each step removes at most one candidate.
- It releases a single request at time `0`, on one of the two pages outside the initial cache (the write-up's `u_0`; `v_0` is requested adaptively later), and reaches the write-up's initial state after an auxiliary phase at budget `0` (`PhaseCount.initial`, `Certificate.initial`). Arrivals at time `0` precede every cache action, so the certificate starts from the initial cache itself and the comparator costs at most `B + 1`, giving `OPT <= (2N+2k)/(2k+1) + 1` (`exists_input_quantitative`).
- Phases are counted with the potential `2|L| + [no mark]` (`PhaseCount.Certificate.potential`, `PhaseCount.budget_bound`) rather than by short and long phases.
- It does not assume that the algorithm moves only at deadlines; onlineness is used directly.

`Model.lean` has no hard deadlines, only continuous, unbounded delay curves. A curve charges `rate * overshoot`, so charging a whole unit within an overshoot of `eps` needs `rate >= 1/eps`; the construction squeezes its requests into a bounded interval, so rates grow as windows shrink. In exchange, the adversary never waits for service: two requests are charged separately as soon as they ask for different pages or have disjoint charging windows. The certificate needs no change, no deadline constraint on auxiliary requests, and only `k >= 1` rather than `k >= 2`.
