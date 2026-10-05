# Lean formalization for uniform paging with delay

This repository formalizes results on uniform paging with delay and with deadlines in Lean 4, with cache size `k`. All results are stated in [`PagingWithDelay.lean`](PagingWithDelay.lean).

Paging with delay:

- FIFO with threshold `1` is nonclairvoyant, online and strictly `(2k+2)`-competitive, and this analysis is tight: no positive threshold makes FIFO better than `(2k+2)`-competitive, given at least `k+2` pages.
- No online algorithm is better than `(2k+1)`-competitive, already on `k+1` pages; this lower bound is not original but due to [Krnetić, Melnyk, Wang and Wattenhofer (ISAAC 2020)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ISAAC.2020.61). On at most `k+1` pages it is matched: FIFO with threshold `(k+1)/k` is strictly `(2k+1)`-competitive.

Paging with deadlines:

- No online algorithm is better than `(k+1/2)`-competitive, given `k+2` pages.
- By the same analysis as for delay, deadline-triggered FIFO is nonclairvoyant, online and strictly `(k+1)`-competitive, and strictly `k`-competitive on at most `k+1` pages.

Lower bounds hold with arbitrary additive constants. Build with `lake build`.

## What to read

To audit the statements rather than the proofs, read:

- [`PagingWithDelay.lean`](PagingWithDelay.lean): the seven theorem statements;
- [`Model.lean`](Model.lean): the definitions they use;
- [`EventLoop.lean`](EventLoop.lean) and [`Algorithm.lean`](Algorithm.lean): the FIFO event loop and its packaging as an algorithm, to check that the algorithm named by the results is the intended one.

Everything else is machine-checked proof implementation.

## Model

An `Instance` consists of a cache size `k > 0`, an initial cache of `k` distinct pages (the common full initial cache `C₀` of the write-up, whose order is FIFO's initial queue), and requests in nondecreasing arrival order. Each `Request` has a page, an arrival time and a continuous, monotone, unbounded delay curve starting at `0`. `Instance.pageUniverse` is the finite set of pages in the initial cache or requested.

A `Schedule` is a list of fetch events starting from the initial cache at no cost; its cost is the number of fetches plus the delay of every request until it is served. `Schedule.Feasible` collects the conditions on a valid schedule; it allows an event to evict several pages. An `Algorithm` maps every instance to a schedule and carries a proof that the schedule is feasible, so neither the conditions on instances nor feasibility appear as hypotheses in the theorems.

An algorithm is _online_ (`Algorithm.Online`) when its schedule up to time `t` is determined by the requests that have arrived by `t`, and _nonclairvoyant_ (`Algorithm.Nonclairvoyant`) when it is determined by less: the delay those requests have accrued by `t`, rather than their delay curves. Nonclairvoyance implies onlineness (`Algorithm.Nonclairvoyant.online`) and is strictly stronger.

`Algorithm.Competitive algorithm ratio inputs` asks for an additive constant `additive : ℕ → Cost` such that `ALG <= ratio k * cost(comparator) + additive k` for every comparator `Algorithm` and every input with cache size `k` satisfying `inputs` (all instances by default; some results restrict the page universe). `Algorithm.StrictlyCompetitive` is the same with additive constant `0`. Comparators range over all algorithms, online or not, so this is the bound against `OPT`; `Algorithm.StrictlyCompetitive.le_of_feasible` recovers it against every feasible schedule.

### Deadlines

To reuse the formalization, the deadline of a request (`Request.deadline`) is modeled as the last time its delay is still zero. A `DeadlineAlgorithm` is an algorithm that meets every deadline on every instance, so its cost is its number of fetches. `DeadlineAlgorithm.Competitive` and `DeadlineAlgorithm.StrictlyCompetitive` compare it with every deadline algorithm.

`Algorithm.Nonclairvoyant` is too strong for deadline algorithms: a deadline at `t` shows in the delay only after `t`, so a request would have to be served on arrival. `DeadlineAlgorithm.Nonclairvoyant` instead lets an algorithm learn a deadline when it is reached: its schedule up to `t` is determined by the requests that have arrived by `t` and those of their deadlines that are at most `t` (`Request.DeadlineAgreeUpTo`). It also implies onlineness (`DeadlineAlgorithm.Nonclairvoyant.online`).

## FIFO

The event loop in `EventLoop.lean` keeps the cache as the pages of the most recent payments and is parameterized by what triggers a fetch (`FIFO.Trigger`): `.threshold δ` fetches a page when its pending delay first reaches `δ`, and `.deadline` fetches it when one of its pending requests reaches its deadline. Ties are resolved explicitly: arrivals at time `t` precede payments at `t`, pages reaching the threshold simultaneously are ordered by their first pending request, and simultaneous arrivals keep list order.

`FIFO.algorithm threshold` in `Algorithm.lean` runs the loop with threshold `threshold k` on instances with cache size `k`, and `FIFO.deadlineAlgorithm` with the deadline trigger. For every trigger, independently of the competitive analysis, the formalization proves feasibility (`FIFO.schedule_feasible`), onlineness, nonclairvoyance in the respective sense, and the cost identity `ALG = (1+δ)M` (`FIFO.algorithmCostClaim`), where `M` is the number of payments and `δ = 0` for deadlines. No behavioral property of FIFO is assumed; all are proved from the implementation.

## Proofs

### Paging with delay: the `2k+2` upper bound

`paging_with_delay_upper_bound`: FIFO with threshold `1` is nonclairvoyant, online and strictly `(2k+2)`-competitive. A rank potential is run against the comparator, read through a _lazy cache_ that evicts a page only when its slot is needed (the write-up's "we may assume that OPT evicts a page only when fetching"). Payment windows, the potential changes at online payments and offline fetches, and the three charging cases give the payment accounting `M + Φ_final - Φ_0 <= (k+1) S + ((k+1)/δ) D` for every positive threshold; at `δ = 1` this gives `ALG = 2M <= (2k+2) OPT`. The write-up's potential is `Φ = Σ_{q ∈ C_ALG \ C_OPT} rank(q)` with `Φ_0 = 0`; the proof works with its complement `K - Φ = Σ_{q ∈ C_ALG ∩ C_OPT} rank(q)`, and `payment_accounting_missing` restates the accounting in the write-up's form. Only this charging argument specializes to `δ = 1`. See [`Proofs/RankPotential/README.md`](Proofs/RankPotential/README.md) for the correspondence with the write-up's lemmas.

### Paging with delay: tightness for threshold FIFO

`FIFO_lower_bound`: for every threshold `δ > 0` and `ratio k < 2k+2` at some `k >= 1`, given at least `k+2` pages, threshold FIFO is not `ratio`-competitive. The proof replays FIFO on a family of adversarial instances and exhibits a feasible offline comparator (`Proofs/LowerBound/`). At threshold `0` payments occur on arrival and the construction does not apply.

### Paging with delay: the `2k+1` lower bound

`paging_with_delay_general_lower_bound`: given at least `k+1` pages, no online algorithm is `ratio`-competitive with `ratio k < 2k+1` at some `k >= 1`, already on inputs with `input.pageUniverse.card <= input.cacheSize + 1`, that is, the `k` initially cached pages and at most one more. This result is from Krnetić, Melnyk, Wang and Wattenhofer, [_The k-Server Problem with Delays on the Uniform Metric Space_](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ISAAC.2020.61), ISAAC 2020, and is formalized here following the write-up. The adversarial input is built from the algorithm's own run: each phase requests a page the algorithm does not hold and ends when it is served. The algorithm is compared with the write-up's `k+1` static and `k` dynamic offline strategies by averaging. See [`Proofs/GeneralLowerBound/README.md`](Proofs/GeneralLowerBound/README.md).

### Paging with delay: a matching upper bound on `k+1` pages

`paging_with_delay_upper_bound_k_plus_one_pages`: FIFO with threshold `(k+1)/k` is nonclairvoyant, online and strictly `(2k+1)`-competitive on the same inputs as the lower bound, so on `k+1` pages the competitive ratio is exactly `2k+1`. The proof (`Proofs/KPlusOne/`) reuses the payment accounting with the write-up's stronger offline potential change on `k+1` pages: only `k` is charged per offline fetch, giving `M <= k OPT` and `ALG <= (2k+1) OPT`.

### Paging with deadlines: the `k+1/2` lower bound

`paging_with_delay_deadline_lower_bound`: given at least `k+2` pages, no online deadline algorithm is `ratio`-competitive with `ratio k < k+1/2` at some `k >= 1`. The proof shows more: `DeadlineLowerBound.competitive_ratio_lower_bound_pageUniverse` holds for every online `Algorithm`, which may miss deadlines and pay delay, against a feasible comparator schedule of zero delay cost, on inputs with at most `k+2` pages. Neither this result nor the `2k+1` lower bound implies the other.

The adversary keeps an offline _certificate_ (a distinguished node, a set of cheap candidate configurations, a mark and a budget) alongside the input it builds. Each operation requests a page the algorithm does not hold, costing it a fetch or a unit of delay; the certificate processes it for free or pays one unit and refills its candidates. A payment out of a marked candidate refills `k` candidates and clears the mark, an unmarked one refills `k+1` and sets it, so phases average `k+1/2` operations per payment. See [`Proofs/DeadlineLowerBound/README.md`](Proofs/DeadlineLowerBound/README.md).

### Paging with deadlines: upper bounds for FIFO

`paging_with_delay_deadline_upper_bound` and `paging_with_delay_deadline_upper_bound_k_plus_one_pages`: `FIFO.deadlineAlgorithm` is a nonclairvoyant, online deadline algorithm that is strictly `(k+1)`-competitive, and strictly `k`-competitive on at most `k+1` pages. With the lower bound, the deterministic competitive ratio of paging with deadlines on `k+2` pages lies in `[k+1/2, k+1]`. Both bounds reuse the charging argument for delay, which does not depend on what triggers a payment. Case 3 cannot occur: some request served at a payment has its deadline there, while in Case 3 the comparator serves it strictly later. This gives `M + Φ_final - Φ_0 <= (k+1) S`, and `<= k S` on `k+1` pages (`Proofs/DeadlineUpperBound/`). The write-up's matching lower bound of `k` on `k+1` pages is classical paging and is not formalized.

## Repository layout

| Path                            | Purpose                                                                                                                                                                    |
| ------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `PagingWithDelay.lean`          | Public theorem statements                                                                                                                                                  |
| `Model.lean`                    | Problem and schedule semantics (trusted)                                                                                                                                   |
| `EventLoop.lean`                | FIFO event loop, triggered by a threshold or by deadlines                                                                                                                  |
| `Algorithm.lean`                | FIFO as an `Algorithm`, threshold chosen from the cache size; deadline-triggered FIFO as a `DeadlineAlgorithm`                                                             |
| `Proofs/Basic/`                 | `pageUniverse` lemmas; onlineness and nonclairvoyance in general                                                                                                           |
| `Proofs/Basic/Competitive.lean` | Bridge between comparator schedules and comparator algorithms (`Algorithm.patch`, `strictlyCompetitive_of_schedules`, `not_competitive_of_schedules`, and their converses) |
| `Proofs/FIFO/`                  | Feasibility, onlineness and nonclairvoyance of FIFO, for every trigger                                                                                                     |
| `Proofs/FIFO/Deadlines.lean`    | Deadline-triggered FIFO meets every deadline                                                                                                                               |
| `Proofs/EventLoop/`             | Run invariants and service accounting of the event loop                                                                                                                    |
| `Proofs/Competitive/`           | `ALG = (1+δ)M` and delay bookkeeping                                                                                                                                       |
| `Proofs/RankPotential/`         | Rank-potential proof of the `2k+2` upper bound                                                                                                                             |
| `Proofs/KPlusOne/`              | Improved bound for `k+1` pages, same accounting                                                                                                                            |
| `Proofs/LowerBound/`            | Tightness construction and comparator                                                                                                                                      |
| `Proofs/GeneralLowerBound/`     | General `2k+1` lower bound for all algorithms                                                                                                                              |
| `Proofs/DeadlineUpperBound/`    | `k+1` and `k`-on-`k+1`-pages bounds for deadline-triggered FIFO                                                                                                            |
| `Proofs/DeadlineLowerBound/`    | `k+1/2` lower bound for paging with deadlines                                                                                                                              |
| `Proofs/Analysis/`              | Reusable potential, rank, and cache-trace tools                                                                                                                            |
| `Checks/`                       | Sanity checks on the statements (not part of the library)                                                                                                                  |

## Formalization status

The project builds without `sorry`, added axioms, `native_decide`, or `unsafe`. For the seven public results, `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

The separate library `Checks` (built with `lake build Checks`, not by `lake build`) contains sanity checks on the statements. [`Checks/OnlineExamples.lean`](Checks/OnlineExamples.lean) shows that onlineness and nonclairvoyance are neither vacuous nor trivial, including an online but clairvoyant algorithm separating the two. [`Checks/StatementChecks.lean`](Checks/StatementChecks.lean) derives explicit forms of the public statements from their `Competitive` phrasing: bounds against every feasible comparator schedule, and for deadlines against every feasible schedule meeting all deadlines.
