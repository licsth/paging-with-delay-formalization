# General lower bound: proof status

The general `2k+1` lower bound is **proved**. `PagingWithDelay.lean` states it
as `paging_with_delay_general_lower_bound`; `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`. Nothing in this directory uses
`sorry` or additional axioms, and the trusted files `Model.lean` and
`Algorithm.lean` are unchanged.

## Components

Supporting modules outside this directory:

- `Analysis/Averaging.lean`: finite-family averaging, strict violations with an
  additive constant, and the asymptotic reduction for aggregate cost arbitrarily
  close to online cost. This module does not depend on paging definitions.
- `Analysis/GeometricDelay.lean`: legal positive linear delay curves, a growth
  rate for every positive error tolerance, and the geometric phase estimate.
- `Analysis/Adaptive.lean`: closed-prefix agreement determines the cache before
  an arrival; appending a request preserves that cache and all earlier events.
- `Analysis/Preserve.lean`: appending a request also preserves the *service* of
  every request already served before the new arrival, hence its delay cost.
- `Analysis/CacheFill.lean`: feasible initial cache filling with one fetch per
  page, and concatenation of valid event traces.

In this directory:

- `Adversary.lean`: input extension against an arbitrary feasible online
  algorithm, forcing arbitrarily many fetches on a fixed `k+1`-page universe.
  This is the unbounded-cost construction with long gaps; the tight argument in
  `Phases.lean` uses short gaps instead.
- `Static.lean`: the actual static comparator schedules, their feasibility from
  empty caches, and their summed cost bound by terminal delay plus `(k+1)^2`.
- `Dynamic.lean`: `k` dynamic schedules with distinct holes; each request causes
  at most one movement in the family. The schedules are feasible, serve every
  request at arrival, and have aggregate cost at most `k^2 + requests.length`.
- `Comparators.lean`: combines the static and dynamic schedules on the same
  input into an actual `ComparisonFamily` indexed by `Fin (2*k+1)`, and proves
  the aggregate estimate from a request-count bound and a terminal-delay bound.
- `Averaging.lean`: the paging-specific reduction from a family of `2k+1`
  feasible comparators to a strict violation of any smaller ratio.
- `Phases.lean`: the adaptive request sequence itself.
- `Final.lean`: iterates the phases and discharges the comparator hypotheses.

## The construction in `Phases.lean`

`AdversaryRun` is the invariant carried from phase to phase. A phase issues one
request, on a page the algorithm does not hold immediately before the arrival,
and ends when the algorithm serves it. Recorded in the invariant:

- every request so far is served by the current time `now`, and each phase has
  forced one further fetch stamped no later than `now` (so the algorithm fetches
  at least once per request);
- delay rates grow geometrically, so all earlier rates together are at most `ε`
  times the rate `nextSlope` of the next request;
- holding *every* request until `now` — what the static strategies of
  `Static.lean` do — costs at most `(1+ε)` times the algorithm's own delay plus
  a spent budget `used`, which never exceeds `1`.

The gap between the end of a phase and the next arrival must be positive:
`Model.lean` processes arrivals before transitions with the same timestamp, so
requesting a page exactly when it is evicted can give the algorithm a cache hit.
Each gap is chosen small enough to spend at most half of the remaining budget,
which keeps the total perturbation below `1` for every number of phases.

Onlineness enters twice: `Online.appendRequest_cacheBefore` makes the new
request a miss, and `Online.appendRequest_prefix` together with
`Online.appendRequest_serviceTime` preserves the earlier fetches, service times,
and delay costs, so the invariant of the previous phase still speaks about the
extended run.

`Final.lean` runs the phases `n` times, feeds the resulting input to
`exists_comparisonFamily_of_delay_bound`, and applies
`competitive_ratio_lower_bound_of_families`. The additive overhead is
`k² + (k+1)² + 1`, independent of the number of phases: `k²` for filling the
dynamic caches, `(k+1)²` for the static ones, and `1` for all gap perturbations
together.
