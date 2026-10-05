# Lean formalization for uniform paging with delay

This repository formalizes results on uniform paging with delay
in Lean 4. The central result is that threshold-one FIFO is a nonclairvoyant,
feasible, `(2k+2)`-competitive algorithm for paging with delay.

The formalization also includes further results:

- the analysis is tight for threshold FIFO on page universes of size at least
  `k+2`;
- on a universe of at most `k+1` pages, FIFO with threshold `(k+1)/k` has
  competitive ratio `2k+1`, with no additive constant;
- that ratio is optimal: no deterministic online algorithm is better than
  `(2k+1)`-competitive, already on `k+1` pages;
- for paging with *deadlines*, deadline-triggered FIFO is nonclairvoyant and
  strictly `(k+1)`-competitive, and strictly `k`-competitive on `k+1` pages;
  and
- on `k+2` pages, no deterministic online algorithm for paging with
  deadlines is better than `(k+1/2)`-competitive.

All seven results are stated in [`PagingWithDelay.lean`](PagingWithDelay.lean).
Build the project with:

```sh
lake build
```

## Main result

`paging_with_delay_upper_bound` constructs an algorithm that is nonclairvoyant
and online and proves

```lean
algorithm.StrictlyCompetitive fun k => 2 * k + 2
```

that is, for every input, with cache size `k`, and every comparator algorithm,

```text
ALG <= (2k+2) * cost(comparator).
```

Comparators are algorithms that may be offline, so this is the bound against
`OPT`; `Algorithm.StrictlyCompetitive.le_of_feasible` recovers it against every
feasible comparator schedule.

The witness is FIFO with threshold `1`, `FIFO.algorithm fun _ => 1`. More
generally, the event loop in `EventLoop.lean` is parameterized by what triggers
a fetch (`FIFO.Trigger`): an arbitrary nonnegative threshold `δ : Cost`
(`.threshold δ`, a page is fetched when its pending delay first reaches `δ`), or
deadlines (`.deadline`, a page is fetched when one of its pending requests
reaches its deadline). `FIFO.algorithm threshold` in `Algorithm.lean` runs it
with threshold `threshold k` on instances with cache size `k`, and
`FIFO.deadlineAlgorithm` with the deadline trigger. The formalization proves independently of the competitive analysis
that:

```text
FIFO.schedule_feasible trigger    -- packaged as FIFO.algorithm threshold
FIFO.algorithm_online threshold
FIFO.algorithm_nonclairvoyant threshold
FIFO.algorithmCostClaim (.threshold δ) : ALG = (1+δ) * number_of_payments
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

Competitiveness is defined in `Model.lean` as well. As in the write-up, the
ratio and the additive constant are functions of the cache size `k`.
`Algorithm.Competitive algorithm ratio inputs` asks for additive constants
`additive : ℕ → Cost` such that, for every comparator `Algorithm` and every
input satisfying the predicate `inputs`, with cache size `k`,
`ALG <= ratio k * cost(comparator) + additive k`;
`Algorithm.StrictlyCompetitive` is the same with additive constant `0`.
Comparators range over all algorithms, online or not, so a bound against all of
them is the usual bound against the offline optimum `OPT`. The predicate
`inputs` is all instances by default; some results bound the page universe in
terms of the cache size. For paging with deadlines,
a `DeadlineAlgorithm` is an algorithm that serves every request while its delay
is still zero, that is, meets every deadline on every instance, and
`DeadlineAlgorithm.Competitive` and `DeadlineAlgorithm.StrictlyCompetitive`
compare a deadline algorithm with every deadline algorithm. The deadline of a
request (`Request.deadline`) is the last time its delay is still zero.

An algorithm is *online* when what it does up to a time `t` is determined by
the requests that have arrived by `t`, and *nonclairvoyant* when it is
determined by less: the delay those requests have accrued by `t`, rather than
the delay curves producing it. `Algorithm.Nonclairvoyant` states this by
comparing two instances that have revealed the same thing by `t`, so no
continuation of a truncated delay curve has to be named or assumed to exist.
Nonclairvoyance implies onlineness (`Algorithm.Nonclairvoyant.online`) and is
strictly stronger; `Checks/OnlineExamples.lean` exhibits an algorithm separating
them.

For deadline algorithms this notion is too strong: a deadline at `t` shows in
the delay only after `t`, so an algorithm must serve each request while it
cannot yet tell whether its deadline has come, that is, on arrival. As in
nonclairvoyant paging with deadlines, `DeadlineAlgorithm.Nonclairvoyant`
instead lets an algorithm learn a deadline when it is reached: what it does up
to `t` is determined by the requests that have arrived by `t` and those of
their deadlines that are at most `t` (`Request.DeadlineAgreeUpTo`). It too
implies onlineness (`DeadlineAlgorithm.Nonclairvoyant.online`).

For readers auditing the statement rather than the proof, the essential files
are:

- [`PagingWithDelay.lean`](PagingWithDelay.lean), containing the seven public
  theorem statements; and
- [`Model.lean`](Model.lean), containing the
  definitions appearing in those statements.

To verify that the algorithm named by the results is the intended FIFO event
loop, also read [`EventLoop.lean`](EventLoop.lean), the event loop itself, and
[`Algorithm.lean`](Algorithm.lean), which turns it into an `Algorithm`.
The remaining files are machine-checked proof implementation.

## Proof overview

The FIFO event loop records arrivals and threshold payments while maintaining
the cache as the pages of the most recent payments. From the run invariants the
formalization derives, for both triggers, termination, feasibility,
onlineness, nonclairvoyance (in the respective sense), and the identity
`ALG = (1+δ)M`, where `M` is the number of payments and `δ` is the threshold,
`0` for deadlines.

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
all proved from the implementation in `EventLoop.lean`.

## Additional results

### Tightness of threshold FIFO

`FIFO_lower_bound` proves that for every positive threshold `δ`, threshold
FIFO cannot achieve a competitive ratio below `2k+2`, even with arbitrary
additive constants: `¬ (FIFO.algorithm δ).Competitive ratio` for every
`ratio : ℕ → Cost` with `ratio k < 2k+2` at some cache size `k >= 1`, as soon as
the page type has at least `k+2` pages. The proof constructs a family of adversarial instances,
replays FIFO on them, and exhibits a feasible offline comparator. Its
implementation is in `Proofs/LowerBound/`.

The restriction to positive thresholds is intentional: at threshold zero
payments occur on arrival and the construction no longer describes the run.

### A universe of `k+1` pages

`paging_with_delay_upper_bound_k_plus_one_pages` proves that FIFO with
threshold `(k+1)/k` on instances with cache size `k`
(`FIFO.algorithm fun k => (k+1)/k`) is
strictly `(2k+1)`-competitive on the inputs with
`input.pageUniverse.card <= input.cacheSize + 1`:

```text
ALG <= (2k+1) * cost(comparator)
```

for every comparator algorithm on every such input, that is, on inputs involving at most `k+1` distinct
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

`paging_with_delay_general_lower_bound` proves that _every_ algorithm that is
`Algorithm.Online` fails every competitive claim that falls below `2k+1` at some
cache size `k >= 1`, with arbitrary additive constants, already on inputs with
`input.pageUniverse.card <= input.cacheSize + 1`, as soon as the page type has
at least `k+1` pages: `¬ algorithm.Competitive ratio …` for every
`ratio : ℕ → Cost` with `ratio k < 2k+1`. The adversarial input is built adaptively from the algorithm's own
run: each phase requests a page the algorithm does not currently hold and ends
when the algorithm serves that request. The algorithm is then compared against
the `k+1` static and `k` dynamic offline strategies of the write-up by
averaging. The implementation is in `Proofs/GeneralLowerBound/`; see
the [README](Proofs/GeneralLowerBound/README.md) there.

Together with the previous result this is tight: on `k+1` pages the competitive
ratio of paging with delay is exactly `2k+1`: both statements restrict the
input by the same condition `input.pageUniverse.card <= input.cacheSize + 1`.

### FIFO for paging with deadlines

`paging_with_delay_deadline_upper_bound` proves that deadline-triggered FIFO,
`FIFO.deadlineAlgorithm` (defined in [`Algorithm.lean`](Algorithm.lean)), is a
nonclairvoyant, online deadline algorithm that is strictly
`(k+1)`-competitive against every deadline algorithm, and
`paging_with_delay_deadline_upper_bound_k_plus_one_pages` that it is strictly
`k`-competitive on the inputs with
`input.pageUniverse.card <= input.cacheSize + 1`. Both costs are fetch counts:
FIFO pays once per fetch, `ALG = M`.

As in the write-up, both bounds come from the charging argument of the main
result: deadline-triggered FIFO runs the same event loop with a different
trigger, and payment windows, the rank potential and the potential changes do
not depend on what triggers a payment. What changes is that Case 3 cannot
occur: one of the requests served at a payment has its deadline at the
payment, while in Case 3 the comparator serves it strictly after it, so a
comparator meeting every deadline has no Case-3 payment. This gives the write-up's deadline accounting
`M + Φ_final - Φ_0 <= (k+1) S`, and `M + Φ_final - Φ_0 <= k S` on `k+1`
pages. The implementation is in `Proofs/DeadlineUpperBound/Final.lean`.

The write-up's matching lower bound of `k` on `k+1` pages is classical
paging and is not formalized.

### A lower bound for paging with deadlines

`paging_with_delay_deadline_lower_bound` is the bound for deadlines. _Every_
online `DeadlineAlgorithm` fails every competitive claim that falls below
`k+1/2` at some cache size `k >= 1`, with arbitrary additive constants, as soon
as the page type has at least `k+2` pages: `¬ algorithm.Competitive ratio` for
every `ratio : ℕ → Cost` with `2 * ratio k < 2k+1`. Both sides are deadline algorithms, as in the
write-up: the online algorithm and every comparator serve each request while
its delay is still zero, so both costs are simply fetch counts.
`FIFO.deadlineAlgorithm` shows that online deadline algorithms exist, so the
statement is not vacuous. Together with the previous result, the deterministic
competitive ratio of paging with deadlines on `k+2` pages lies in
`[k+1/2, k+1]`.

The proof establishes more:
`DeadlineLowerBound.competitive_ratio_lower_bound_pageUniverse` holds for every
online `Algorithm`, which may miss a deadline and pay delay, against a feasible
comparator schedule of zero delay cost. The public theorem states only the
deadline form of the write-up.

The construction uses only the `k+2` pages the embedding supplies;
`competitive_ratio_lower_bound_pageUniverse` records that its inputs involve at
most `k+2` pages (at most, because which pages the adversary requests is decided
by the algorithm's own evictions). Neither this result nor the general lower bound
implies the other: there the curves are arbitrary and the universe has `k+1`
pages, here algorithm and comparators are deadline algorithms and the universe
has `k+2`.

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

The four files a reader of the statements needs are at the top level; all
proofs are under `Proofs/`, and sanity checks on the statements under
`Checks/`.

| Path                         | Purpose                                         |
| ---------------------------- | ----------------------------------------------- |
| `PagingWithDelay.lean`       | Public theorem statements                       |
| `Model.lean`                 | Problem and schedule semantics (trusted)        |
| `EventLoop.lean`             | FIFO event loop, triggered by a threshold or by deadlines |
| `Algorithm.lean`             | FIFO as an `Algorithm`, threshold chosen from the cache size; deadline-triggered FIFO as a `DeadlineAlgorithm` |
| `Proofs/Basic/`              | `pageUniverse` lemmas; onlineness and nonclairvoyance in general |
| `Proofs/Basic/Competitive.lean` | Bridge between comparator schedules and comparator algorithms (`Algorithm.patch`, `strictlyCompetitive_of_schedules`, `not_competitive_of_schedules`, and their converses) |
| `Proofs/FIFO/`               | Feasibility, onlineness and nonclairvoyance of FIFO, for every trigger |
| `Proofs/FIFO/Deadlines.lean` | Deadline-triggered FIFO meets every deadline |
| `Proofs/EventLoop/`          | Run invariants and service accounting of the event loop |
| `Proofs/Competitive/`        | `ALG = (1+δ)M` and delay bookkeeping            |
| `Proofs/RankPotential/`      | Rank-potential proof of the main upper bound    |
| `Proofs/KPlusOne/`           | Improved bound for `k+1` pages, same accounting |
| `Proofs/LowerBound/`         | Tightness construction and comparator           |
| `Proofs/GeneralLowerBound/`  | General `2k+1` lower bound for all algorithms   |
| `Proofs/DeadlineUpperBound/` | `k+1` and `k`-on-`k+1`-pages bounds for deadline-triggered FIFO |
| `Proofs/DeadlineLowerBound/` | `k+1/2` lower bound for deadline delays         |
| `Proofs/Analysis/`           | Reusable potential, rank, and cache-trace tools |
| `Checks/`                    | Sanity checks on the statements (not part of the library) |

## Formalization status

The project builds without `sorry`, added axioms, `native_decide`, or `unsafe`.
For the seven public results, `#print axioms` reports only the standard
foundational dependencies `propext`, `Classical.choice`, and `Quot.sound`.

Small examples in [`Checks/OnlineExamples.lean`](Checks/OnlineExamples.lean) check that the definitions of
onlineness and nonclairvoyance are neither vacuous nor trivial — including an
algorithm that is online but clairvoyant, which separates the two — and
[`Checks/StatementChecks.lean`](Checks/StatementChecks.lean) derives the
explicit forms of the public statements — bounds against every feasible
comparator schedule, and for deadlines against every feasible schedule meeting
all deadlines — from their `Competitive` phrasing. They form the separate library `Checks`, which
`lake build` does not compile; check them with `lake build Checks`.
