# Lean formalization for uniform paging with delay

This repository formalizes results on uniform paging with delay
in Lean 4. The central result is that threshold-one FIFO is a nonclairvoyant,
feasible, `(2k+2)`-competitive algorithm for paging with delay.

The formalization also includes four refinements:

- the analysis is tight for threshold FIFO on page universes of size at least
  `k+2`;
- on a universe of at most `k+1` pages, FIFO with threshold `(k+1)/k` has
  competitive ratio `2k+1`, with no additive constant;
- that ratio is optimal: no deterministic online algorithm is better than
  `(2k+1)`-competitive, already on `k+1` pages; and
- on `k+2` pages, no deterministic online algorithm is better than
  `(k+1/2)`-competitive against a comparator that serves every request at zero
  delay cost — the bound for paging with *deadlines*.

All five results are stated in [`PagingWithDelay.lean`](PagingWithDelay.lean).
Build the project with:

```sh
lake build
```

## Main result

`paging_with_delay_upper_bound` constructs an algorithm that is nonclairvoyant
and online and proves, for every input and every feasible comparator,

```text
ALG <= (2k+2) * cost(comparator).
```

The witness is FIFO with threshold `1`. More generally, the implementation in
`Algorithm.lean` is parameterized by an arbitrary nonnegative threshold
`δ : Cost`, and the formalization proves independently of the competitive
analysis that:

```text
FIFO.schedule_feasible δ          -- packaged as the algorithm FIFO.algorithm δ
FIFO.algorithm_online δ
FIFO.algorithm_nonclairvoyant δ
FIFO.algorithmCostClaim δ : ALG = (1+δ) * number_of_payments
```

Only the charging argument establishing the `2k+2` ratio specializes to
`δ = 1`.

## Model and scope

The definitions in `Model.lean` describe request instances, schedules, cost,
feasibility, algorithms, onlineness, and nonclairvoyance. An `Instance` carries
the conditions under which paging is meaningful (requests in arrival order, a
positive cache size, a full initial cache), and an `Algorithm` carries a proof
that every instance receives a feasible schedule, so neither appears as a
hypothesis in the theorems. Every instance supplies the
common full initial cache `C₀` of the write-up (`Instance.initialCache`, a list
of `cacheSize` distinct pages whose order is the initial FIFO queue); every
schedule, online or offline, starts from it at no cost, and
`Instance.pageUniverse` counts its pages. Requests are presented in
nondecreasing arrival order, and comparator evictions occur at fetch events.
These choices match the proof development while preserving the competitive
claims in the write-up.

The event loop resolves ties explicitly: arrivals at time `t` precede payments
at `t`; pages reaching the threshold simultaneously are ordered by their first
pending request; simultaneous arrivals retain list order.

An algorithm is *online* when what it does up to a time `t` is determined by
the requests that have arrived by `t`, and *nonclairvoyant* when it is
determined by less: the delay those requests have accrued by `t`, rather than
the delay curves producing it. `Algorithm.Nonclairvoyant` states this by
comparing two instances that have revealed the same thing by `t`, so no
continuation of a truncated delay curve has to be named or assumed to exist.
Nonclairvoyance implies onlineness (`Algorithm.Nonclairvoyant.online`) and is
strictly stronger; `Checks/OnlineExamples.lean` exhibits an algorithm separating
them.

For readers auditing the statement rather than the proof, the essential files
are:

- [`PagingWithDelay.lean`](PagingWithDelay.lean), containing the five public
  theorem statements; and
- [`Model.lean`](Model.lean), containing the
  definitions appearing in those statements.

To verify that the algorithm named by the results is the intended FIFO event
loop, also read [`Algorithm.lean`](Algorithm.lean).
The remaining files are machine-checked proof implementation.

## Proof overview

The FIFO event loop records arrivals and threshold payments while maintaining
the cache as the pages of the most recent payments. From the run invariants the
formalization derives termination, feasibility, onlineness, nonclairvoyance,
and the identity
`ALG = (1+δ)M`, where `M` is the number of payments.

For the main upper bound, a rank potential is run against the comparator, read through
a *lazy cache* that evicts a page only when its slot is needed (the write-up's
"we may assume that OPT evicts a page only when fetching"; `Schedule.Feasible`
itself allows an event to evict several pages). Payment windows, the potential
changes at online payments and offline fetches, and the three charging cases
give the payment accounting `M + Φ_final - Φ_0 <= (k+1) S + ((k+1)/δ) D` for
every positive threshold, and at `δ = 1`, `ALG = 2M <= (2k+2) OPT`. The
write-up's potential is `Φ = Σ_{q ∈ C_ALG \ C_OPT} rank(q)`, with `Φ_0 = 0`;
the proof runs on its complement `K - Φ = Σ_{q ∈ C_ALG ∩ C_OPT} rank(q)`, and
`payment_accounting_missing` restates the accounting in the write-up's form. The
implementation is in `Proofs/RankPotential/`; see the
[README](Proofs/RankPotential/README.md) there for the correspondence
with the write-up's lemmas.

No behavioral property of FIFO is assumed: the cache invariant, threshold
attainment, service semantics, feasibility, onlineness, and nonclairvoyance are
all proved from the implementation in `Algorithm.lean`.

## Additional results

### Tightness of threshold FIFO

`FIFO_lower_bound` proves that for every positive threshold,
cache size `k >= 1`, and page type with at least `k+2` pages, threshold FIFO
cannot achieve a competitive ratio below `2k+2`, even with an arbitrary
additive constant. The proof constructs a family of adversarial instances,
replays FIFO on them, and exhibits a feasible offline comparator. Its
implementation is in `Proofs/LowerBound/`.

The restriction to positive thresholds is intentional: at threshold zero,
payments occur on arrival and the construction no longer describes the run.

### A universe of `k+1` pages

`paging_with_delay_upper_bound_k_plus_one_pages` proves that, for `k >= 1`,
FIFO with threshold `(k+1)/k` satisfies

```text
ALG <= (2k+1) * cost(comparator)
```

for every feasible comparator on every input with
`input.pageUniverse.card <= k + 1`, that is, involving at most `k+1` distinct
pages: the `k` initially cached ones and at most one more.
`Instance.pageUniverse`, defined in `Model.lean`, is the finite set of pages
in the initial cache or requested. No assumption on the size of the page type
is needed. There is no additive term: both
schedules start from the common full initial cache, so the write-up's rank
potential starts at `Φ_0 = 0`. The proof, in `Proofs/KPlusOne/Final.lean`, is
the payment accounting of `Proofs/RankPotential/` with the write-up's
stronger offline potential change on `k+1` pages: an offline fetch that evicts
the one page outside FIFO's cache lowers the write-up's potential by at
least one, so
only `k` is charged per offline fetch, and at threshold `(k+1)/k` this gives
`M <= k * OPT` and `ALG <= (2k+1) * OPT`.

### The general lower bound

`paging_with_delay_general_lower_bound` proves that for `k >= 1` and a page type
with at least `k+1` pages, _every_ algorithm that is `Algorithm.Online` fails
every competitive claim below `2k+1`, with an
arbitrary additive constant, already on inputs with
`input.pageUniverse.card <= k + 1`. The adversarial input is built adaptively from the algorithm's own
run: each phase requests a page the algorithm does not currently hold and ends
when the algorithm serves that request. The algorithm is then compared against
the `k+1` static and `k` dynamic offline strategies of the write-up by
averaging. The implementation is in `Proofs/GeneralLowerBound/`; see
the [README](Proofs/GeneralLowerBound/README.md) there.

Together with the previous result this is tight: on `k+1` pages the competitive
ratio of paging with delay is exactly `2k+1`: both statements restrict the
input by the same condition `input.pageUniverse.card <= k + 1`.

### A lower bound for deadline delays

`paging_with_delay_deadline_lower_bound` is the bound for deadlines. For
`k >= 1` and a page type with at least `k+2` pages, _every_ algorithm that is
`Algorithm.Online` fails every competitive claim below
`k+1/2`, with an arbitrary additive constant, on an input with
`input.pageUniverse.card <= k + 2` — and against a comparator that serves every
request at *zero delay cost*.

That last property is what makes it a statement about deadlines, and it
strengthens the claim on both sides. The construction's delay curves are zero
inside a window and grow afterwards, so a schedule of zero delay cost is one
that serves every request inside its window: the comparator misses no deadline.
The algorithm is under no such restriction — it may miss a deadline and pay for
it, which a hard-deadline algorithm cannot do. So even an algorithm allowed to
buy its way out of deadlines cannot beat `k+1/2` against a comparator that never
does. `Checks/StatementChecks.lean` derives the specialisation to algorithms that never
miss a deadline, where both costs are simply fetch counts.

The bound on the universe is `<=` and not `=` because the adversary is not
obliged to touch every page it may use: which pages it requests is decided by
the algorithm's own evictions. Neither this result nor the general lower bound
implies the other: there the curves are arbitrary and the universe has `k+1`
pages, here the curves are deadlines and the universe has `k+2`.

The adversary keeps an offline *certificate* — a distinguished node, a set of
cheap candidate configurations, a mark, and a budget — alongside the input it
builds. Each operation releases one request on a page the algorithm does not
hold, which costs the algorithm a fetch or a unit of delay; the certificate
either processes it for free or pays one unit and refills its candidate set. A
payment out of a marked candidate refills `k` candidates and clears the mark, an
unmarked one refills `k+1` and sets it, so two short phases cannot be
consecutive and phases average `k+1/2` operations per payment. The
implementation is in `Proofs/DeadlineLowerBound/`; see the
[README](Proofs/DeadlineLowerBound/README.md) there.

## Repository layout

The three files a reader of the statements needs are at the top level; all
proofs are under `Proofs/`, and sanity checks on the statements under
`Checks/`.

| Path                         | Purpose                                         |
| ---------------------------- | ----------------------------------------------- |
| `PagingWithDelay.lean`       | Public theorem statements                       |
| `Model.lean`                 | Problem and schedule semantics (trusted)        |
| `Algorithm.lean`             | Threshold-parameterized FIFO event loop         |
| `Proofs/Basic/`              | `pageUniverse` lemmas; onlineness and nonclairvoyance in general |
| `Proofs/FIFO/`               | Feasibility, onlineness and nonclairvoyance of FIFO, for every threshold |
| `Proofs/EventLoop/`          | Run invariants and service accounting of the event loop |
| `Proofs/Competitive/`        | `ALG = (1+δ)M` and delay bookkeeping            |
| `Proofs/RankPotential/`      | Rank-potential proof of the main upper bound    |
| `Proofs/KPlusOne/`           | Improved bound for `k+1` pages, same accounting |
| `Proofs/LowerBound/`         | Tightness construction and comparator           |
| `Proofs/GeneralLowerBound/`  | General `2k+1` lower bound for all algorithms   |
| `Proofs/DeadlineLowerBound/` | `k+1/2` lower bound for deadline delays         |
| `Proofs/Analysis/`           | Reusable potential, rank, and cache-trace tools |
| `Checks/`                    | Sanity checks on the statements (not part of the library) |

## Formalization status

The project builds without `sorry`, added axioms, `native_decide`, or `unsafe`.
For the five public results, `#print axioms` reports only the standard
foundational dependencies `propext`, `Classical.choice`, and `Quot.sound`.

Small examples in [`Checks/OnlineExamples.lean`](Checks/OnlineExamples.lean) check that the definitions of
onlineness and nonclairvoyance are neither vacuous nor trivial — including an
algorithm that is online but clairvoyant, which separates the two — and
[`Checks/StatementChecks.lean`](Checks/StatementChecks.lean) derives the
earlier phrasing of the two universe-restricted theorems from their current
`pageUniverse` phrasing. They form the separate library `Checks`, which
`lake build` does not compile; check them with `lake build Checks`.
