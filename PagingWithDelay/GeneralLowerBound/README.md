# General lower bound: proof status

The general `2k+1` lower bound is **not yet proved**. All Lean results in this
directory are proved without `sorry` or additional axioms, but the conditional
averaging reduction still needs its comparator-family hypothesis discharged.

Completed components:

- `Analysis/Averaging.lean`: finite-family averaging, strict violations with an
  additive constant, and the asymptotic reduction for aggregate cost arbitrarily
  close to online cost. This module does not depend on paging definitions.
- `Analysis/GeometricDelay.lean`: legal positive linear delay curves, a growth
  rate for every positive error tolerance, and the geometric phase estimate.
- `Analysis/Adaptive.lean`: closed-prefix agreement determines the cache before
  an arrival; appending a request preserves that cache and all earlier events.
- `Analysis/CacheFill.lean`: feasible initial cache filling with one fetch per
  page, and concatenation of valid event traces.
- `Adversary.lean`: input extension against an arbitrary feasible online
  algorithm, forcing arbitrarily many fetches on a fixed `k+1`-page universe.
- `Static.lean`: the actual static comparator schedules, their feasibility from
  empty caches, and their summed cost bound by terminal delay plus `(k+1)^2`.
- `Dynamic.lean`: `k` dynamic schedules with distinct holes; each request causes
  at most one movement in the family. The schedules are feasible, serve every
  request at arrival, and have aggregate cost at most `k^2 + requests.length`.
- `Comparators.lean`: combines the static and dynamic schedules on the same
  input into an actual `ComparisonFamily` indexed by `Fin (2*k+1)`. Also proves
  the aggregate estimate from a request-count bound and a terminal-delay bound
  on that input.
- `Averaging.lean`: the paging-specific reduction from a family of `2k+1`
  feasible comparators to a strict violation of any smaller ratio, with any
  additive constant. The required family is an explicit hypothesis.

## Remaining construction

The unbounded-cost inputs in `Adversary.lean` use long gaps (after every event
of the preceding run). They establish unboundedness only; they do not satisfy
the static delay estimate. It would be invalid to combine their unboundedness
with a comparator bound proved on different inputs.

For the tight construction, maintain a prefix whose requests have all been
served by a cutoff `t`. Append a request at `t + gap`, on a page absent from
the old run's cache immediately before that arrival. Choose `gap > 0` small
enough that the extra terminal delay of all older requests is bounded by a
prescribed per-step error. `Online.appendRequest_cacheBefore` proves the new
request is a miss, and `Online.appendRequest_prefix` preserves all earlier
service events. Stop the next phase at the new request's earliest service
time, then repeat. Use geometrically increasing slopes and bound the sum of
gap errors uniformly (for example, by one).

The positive gaps are necessary: `Model.lean` processes arrivals before
transitions at the same timestamp, so requesting a page exactly when it is
evicted can give the online algorithm a cache hit.

The dynamic family is now built from the request sequence alone, even if the
online algorithm prefetches or leaves its cache partly empty. Maintain `k`
distinct offline holes equal to all pages except the most recently requested
page `p`. For the next requested page `q ≠ p`, the unique strategy whose hole
is `q` fetches `q` and changes its hole to `p`; all others stay put. For `q = p`
no strategy moves. With strictly increasing arrival times, every request is
served at arrival. Thus the aggregate dynamic moving cost is at most the
number of requests plus `k^2` for initial cache filling. The adaptive miss
construction must show the online trace has at least one distinct fetch per
request. The construction and all schedule obligations in this paragraph are
proved in `Dynamic.lean`; only the online fetch-count comparison remains.

`exists_comparisonFamily_of_delay_bound` now combines the comparator results:
given one online fetch per request and the terminal-delay estimate, aggregate
comparator cost is at most `(1+ε) ALG` plus a constant depending on `k` and the
gap-error budget. Establish those two estimates and unbounded online cost
for the short-gap inputs, then apply
`competitive_ratio_lower_bound_of_families`. Only then add the unconditional
general lower-bound theorem to `PagingWithDelay.lean`.

The trusted files `Model.lean` and `Algorithm.lean` have not been changed.
