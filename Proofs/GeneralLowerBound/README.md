# The `2k+1` lower bound for paging with delay

`paging_with_delay_general_lower_bound` in [`PagingWithDelay.lean`](../../PagingWithDelay.lean): given at least `k+1` pages, no online algorithm is better than `(2k+1)`-competitive, already on inputs with at most `k+1` pages.

This result is not original: it is due to Krnetić, Melnyk, Wang and Wattenhofer, [_The k-Server Problem with Delays on the Uniform Metric Space_](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ISAAC.2020.61), ISAAC 2020. The adversarial input is built from the algorithm's own run, and the algorithm is compared with `k+1` static and `k` dynamic offline strategies by averaging.

## Components

Supporting modules in `Proofs/Analysis/`:

- `Averaging.lean`: finite-family averaging, strict violations with an additive constant, and the reduction for aggregate cost arbitrarily close to online cost. Independent of paging.
- `GeometricDelay.lean`: positive linear delay curves and a growth rate for every positive error tolerance (`exists_rate_growth`).
- `Adaptive.lean`: agreement on a closed prefix determines the cache before an arrival; appending a request preserves that cache and all earlier events.
- `Preserve.lean`: appending a request preserves the service, hence the delay cost, of every request served before the new arrival.
- `CacheFill.lean`: turning the initial cache into any target cache with one fetch per missing page (`resetEvents`), and concatenation of valid event traces.

In this directory:

- `Static.lean`: the `k+1` static comparator schedules, feasible from the common initial cache, with summed cost at most terminal delay plus `(k+1)^2`.
- `Dynamic.lean`: `k` dynamic schedules with distinct holes, feasible, serving every request at arrival, with aggregate cost at most `k^2 + requests.length`.
- `Comparators.lean`: static and dynamic schedules combined into a `ComparisonFamily` indexed by `Fin (2*k+1)`, with the aggregate estimate.
- `Averaging.lean`: from a family of `2k+1` feasible comparators to a strict violation of any smaller ratio.
- `Phases.lean`: the adaptive request sequence, using short gaps.
- `Final.lean`: iterates the phases and discharges the comparator hypotheses.

## The construction in `Phases.lean`

A phase issues one request on a page the algorithm does not hold immediately before the arrival, and ends when the algorithm serves it. The invariant `AdversaryRun` records:

- every request so far is served by the current time `now`, and each phase has forced one further fetch by `now`, so the algorithm fetches at least once per request;
- delay rates grow geometrically, so all earlier rates together are at most `ε` times the rate `nextSlope` of the next request;
- holding every request until `now` costs at most `(1+ε)` times the algorithm's own delay plus a spent budget `used <= 1`. Summed over all `k+1` static strategies of `Static.lean`, each holding the requests to its own hole, that is holding every request.

The gap between the end of a phase and the next arrival must be positive: arrivals precede transitions with the same timestamp, so requesting a page exactly when it is evicted could give the algorithm a cache hit. Each gap spends at most half of the remaining budget, which keeps the total perturbation below `1`.

Onlineness enters twice: `Online.appendRequest_cacheBefore` makes the new request a miss, and `Online.appendRequest_prefix` with `Online.appendRequest_serviceTime` preserves earlier fetches, service times and delay costs, so the invariant of the previous phase still holds for the extended run.

`Final.lean` runs `n` phases, feeds the input to `exists_comparisonFamily_of_delay_bound`, and applies `competitive_ratio_lower_bound_of_families`. The additive overhead is `k² + (k+1)² + 1`, independent of `n`: `k²` for reaching the dynamic caches from the initial cache, `(k+1)²` for the static ones, and `1` for all gap perturbations.
