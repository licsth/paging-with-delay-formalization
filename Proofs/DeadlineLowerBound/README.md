# The `k + 1/2` lower bound for deadline delays

`paging_with_delay_deadline_lower_bound` in
[`PagingWithDelay.lean`](../../PagingWithDelay.lean): for `k >= 1` and a set of
`k+2` pages, no feasible online algorithm is `(k+1/2-eps)`-competitive, already
on inputs whose delay curves are all of deadline form.  This is Theorem
`thm:deadlines_lower_bound` of `submission.tex`.

The development has six parts, each checkable on its own.

| File | What it settles |
| ---- | --------------- |
| `PhaseCount.lean` | The counting engine: the certificate state `(c, L, q, m)`, its two operations, and `(2k+1) m_T <= 2T + 2k` after `T` operations. The bound is met with equality by an explicit three-operation run, so it cannot be improved. |
| `Offline.lean` | Offline schedules as start configuration plus timed moves, with the service semantics of `Model.lean`. |
| `Certificate.lean` | The offline certificate: every configuration reachable at `m+1`, the cheap ones at `m`, the flagged ones at `m+1` having served the distinguished request — and that the two operations preserve all three. |
| `Bridge.lean` | The translation into `Model.lean`: a move list becomes a `Schedule`, proved `Schedule.Feasible`, of `totalCost` at most the number of moves (it starts from the initial cache) and with zero delay cost. Nothing downstream is trusted in the move-list language. |
| `Charging.lean`, `Online.lean` | The online side: a request whose page is absent on arrival is either served by a fetch inside its window or pays delay, and separated requests charge distinct units, so `ALG >= number of requests`. |
| `Loop.lean`, `Final.lean` | The adaptive construction, maintaining input, certificate and potential together, and the assembly. |

## Notation

The docstrings use the notation of earlier hard-deadline drafts of Section 5.
It corresponds to the write-up as follows.

| Lean / drafts | Write-up (`submission.tex`, Section 5) |
| ------------- | -------------------------------------- |
| distinguished node `c` | held page `h` |
| cheap set `L` | candidate set `𝒞` |
| mark `q` | the starred member of `𝒞` |
| budget `m` | budget `B` |
| `Certificate.background` / `cheap` / `flagged` | invariants `lb_inv_1` / `lb_inv_2` / `lb_inv_3` |
| operation (F), `process` | continuing a phase |
| operation (P), `pay_short` / `pay_long` | starting a new phase, from a starred / unstarred `p` |
| `(2k+1) m_T <= 2T + 2k` | `B <= (2N+2k)/(2k+1)` |

The Lean adversary differs from the write-up's in inessential ways. It starts a
new phase as soon as the only candidate is absent from the online cache, and
otherwise requests any absent page other than `h`; the write-up's choice of `p`
maximizing `|𝒞 \ {p}|` is not needed, since the counting only uses that each
step removes at most one candidate. It releases a single request at time `0`
and reaches the write-up's initial state after an auxiliary phase at budget `0`
(`PhaseCount.initial`, `Certificate.initial`). Its phases are counted with the
potential `2|L| + [no mark]` (`PhaseCount.Certificate.potential`, `PhaseCount.budget_bound`) rather than by short
and long phases. And it does not assume that the algorithm moves only at
deadlines: onlineness is used directly.

## Differences from the hard-deadline drafts

`Model.lean` has no hard deadlines: a delay curve is continuous, real-valued and
unbounded. Three things change as a result.

1. **The penalty rate matters.** A continuous curve charges `rate * overshoot`,
   so charging a whole unit within an overshoot of `eps` needs `rate >= 1/eps`.
   The construction squeezes its requests into a bounded interval, so the rates
   grow as the windows shrink.
2. **The adversary never waits for service.** With hard deadlines the drafts
   need the algorithm to serve a request before its page is reused. Here two
   requests are charged separately as soon as they ask for different pages *or*
   have disjoint charging windows, which the release rule provides directly.
3. **The construction starts at time `0`, from the initial cache.** As in the
   write-up, the initial cache is `k` pages of the universe, and a request is
   released at time `0` on one of the two pages outside it (the write-up's
   `u_0`; the request on `v_0` is released adaptively later). Arrivals at time `0` precede every cache action, so the
   algorithm cannot move first, and the certificate's start configuration is
   the instance's initial cache itself. The comparator therefore needs no
   start-up fetches and costs at most `B + 1`, which gives the write-up's
   quantitative bound `OPT ≤ (2N+2k)/(2k+1) + 1` with no further additive
   constant (`exists_input_quantitative`).

The certificate itself needed no change, and it needs less than the drafts ask:
no deadline constraint on auxiliary requests at all, and `k >= 1` rather than
`k >= 2`.
