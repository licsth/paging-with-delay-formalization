# Lean formalization for uniform paging with delay

This repository formalizes results on uniform paging with delay
in Lean 4. The central result is that threshold-one FIFO is an online, feasible,
`(2k+2)`-competitive algorithm for paging with delay.

The formalization also includes two refinements:

- the analysis is tight for threshold FIFO on page universes of size at least
  `k+2`; and
- on a universe of exactly `k+1` pages, FIFO with threshold `(k+1)/k` has
  competitive ratio `2k+1`, up to an additive constant caused by the model's
  empty initial cache.

All three results are stated in [`PagingWithDelay.lean`](PagingWithDelay.lean).
Build the project with:

```sh
lake build
```

## Main result

`paging_with_delay_upper_bound` constructs an algorithm that is online and
feasible and proves, for every valid input and every feasible comparator,

```text
ALG <= (2k+2) * cost(comparator).
```

The witness is FIFO with threshold `1`. More generally, the implementation in
`Algorithm.lean` is parameterized by an arbitrary nonnegative threshold
`δ : Cost`, and proves independently of the competitive analysis that:

```text
FIFO.schedule_feasible δ
FIFO.schedule_online δ
FIFO.algorithmCostClaim δ : ALG = (1+δ) * number_of_payments
```

Only the charging argument establishing the `2k+2` ratio specializes to
`δ = 1`.

## Model and scope

The definitions in `Model.lean` describe request instances, schedules, cost,
feasibility, and onlineness. Caches start empty, requests are presented in
nondecreasing arrival order, and comparator evictions occur at fetch events.
These choices match the proof development while preserving the competitive
claims in the write-up.

The event loop resolves ties explicitly: arrivals at time `t` precede payments
at `t`; pages reaching the threshold simultaneously are ordered by their first
pending request; simultaneous arrivals retain list order.

For readers auditing the statement rather than the proof, the essential files
are:

- [`PagingWithDelay.lean`](PagingWithDelay.lean), containing the three public
  theorem statements; and
- [`PagingWithDelay/Model.lean`](PagingWithDelay/Model.lean), containing the
  definitions appearing in those statements.

To verify that the algorithm named by the results is the intended FIFO event
loop, also read [`PagingWithDelay/Algorithm.lean`](PagingWithDelay/Algorithm.lean).
The remaining files are machine-checked proof implementation.

## Proof overview

The FIFO event loop records arrivals and threshold payments while maintaining
the cache as the pages of the most recent payments. From the run invariants the
formalization derives termination, feasibility, onlineness, and the identity
`ALG = (1+δ)M`, where `M` is the number of payments.

For the main upper bound at `δ = 1`, payments are assigned to the charging
classes used in the write-up. Payment windows and the FIFO eviction invariant
bound the contribution of each class by the comparator's fetch or delay cost.
Combining the class bounds gives `ALG = 2M <= (2k+2) OPT`.

No behavioral property of FIFO is assumed: the cache invariant, threshold
attainment, service semantics, feasibility, and onlineness are all proved from
the implementation in `Algorithm.lean`.

## Additional results

### Tightness of threshold FIFO

`paging_with_delay_lower_bound` proves that for every positive threshold,
cache size `k >= 1`, and page type with at least `k+2` pages, threshold FIFO
cannot achieve a competitive ratio below `2k+2`, even with an arbitrary
additive constant. The proof constructs a family of adversarial instances,
replays FIFO on them, and exhibits a feasible offline comparator. Its
implementation is in `PagingWithDelay/LowerBound/`.

The restriction to positive thresholds is intentional: at threshold zero,
payments occur on arrival and the construction no longer describes the run.

### A universe of `k+1` pages

`paging_with_delay_upper_bound_k_plus_one_pages` proves that, for `k >= 1`,
FIFO with threshold `(k+1)/k` satisfies

```text
ALG <= (2k+1) * cost(comparator) + (2k+1)^2/k
```

for every feasible comparator when all requests are drawn from a designated
set of exactly `k+1` pages. The write-up uses a common full initial cache and therefore has no
additive term; `Model.lean` starts both schedules empty, producing the explicit
constant above while leaving the asymptotic ratio unchanged. The proof is in
`PagingWithDelay/KPlusOne/`, supported by generic potential and cache-trace
lemmas in `PagingWithDelay/Analysis/`.

## Repository layout

| Path                                | Purpose                                         |
| ----------------------------------- | ----------------------------------------------- |
| `PagingWithDelay.lean`              | Public theorem statements                       |
| `PagingWithDelay/Model.lean`        | Problem and schedule semantics                  |
| `PagingWithDelay/Algorithm.lean`    | Threshold-parameterized FIFO event loop         |
| `PagingWithDelay/EventLoop/`        | Run invariants and service accounting           |
| `PagingWithDelay/Competitive/`      | Charging proof of the main upper bound          |
| `PagingWithDelay/FIFOFeasible.lean` | Feasibility of FIFO for every threshold         |
| `PagingWithDelay/FIFOOnline.lean`   | Onlineness of FIFO for every threshold          |
| `PagingWithDelay/LowerBound/`       | Tightness construction and comparator           |
| `PagingWithDelay/KPlusOne/`         | Improved bound for `k+1` pages                  |
| `PagingWithDelay/Analysis/`         | Reusable potential, rank, and cache-trace tools |

## Formalization status

The project builds without `sorry`, added axioms, `native_decide`, or `unsafe`.
For the three public results, `#print axioms` reports only the standard
foundational dependencies `propext`, `Classical.choice`, and `Quot.sound`.

Small examples in `OnlineExamples.lean` check that the definitions of
feasibility and onlineness are neither vacuous nor trivial.
