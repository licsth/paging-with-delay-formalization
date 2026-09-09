# Lean formalization of `fifo-upper-bound.tex`

Threshold-one FIFO is an online, feasible, `(2k+2)`-competitive algorithm for
paging with delay, and no threshold does better. On a universe of exactly
`k+1` pages the ratio drops to `2k+1`, for FIFO with threshold `(k+1)/k`.
Build with `lake build`. All three theorems are complete — see
[Lower bound](#lower-bound) and [`k+1` pages](#k1-pages).

## The threshold `δ`

The event loop in `Algorithm.lean` is parametric in the threshold `δ : Cost`
(`Cost = NNReal`, so every nonnegative threshold is covered): `thresholdTime δ`,
`nextPayment? δ`, `nextAction? δ`, `run δ`, `schedule δ`. Three theorems hold at
every `δ`:

```text
FIFO.schedule_feasible (δ) (input) (valid) : (FIFO.schedule δ input valid).Feasible input
FIFO.schedule_online   (δ)                 : Algorithm.Online (FIFO.schedule δ)
FIFO.algorithmCostClaim (δ) (input) (valid) :
  (FIFO.schedule δ input valid).totalCost input = (1 + δ) * FIFO.paymentCount δ input valid
```

The last is one fetch plus `δ` units of released delay per payment; at `δ = 1`
it is the paper's `ALG = 2M`. Everything these rest on — the whole `EventLoop/`
layer — carries `δ` as an implicit parameter. Only the charging argument
(payment classes and class bounds) is threshold-one, so the competitive bound
`paging_with_delay_upper_bound` is about `FIFO.schedule 1`. The `k+1`-page
bound uses the same `δ`-parametric layer at `δ = (k+1)/k`.

## Status

The build succeeds. There is no added `axiom`, no `native_decide`, no `unsafe`,
no `sorry`, and `#print axioms` reports only `propext`, `Classical.choice`,
`Quot.sound` for all three of `paging_with_delay_upper_bound`,
`paging_with_delay_lower_bound` and
`paging_with_delay_upper_bound_k_plus_one_pages`.

## What a reader has to check

Trusting the compiler on the proofs, a theorem means what it says iff its
*statement* and the definitions under it are right — for the upper bound,
exactly two files, ~200 lines: `PagingWithDelay.lean` (the theorems) and
`PagingWithDelay/Model.lean` (every definition its statement mentions
transitively, and nothing else). Everything else is proof, and this is
machine-checkable: close the constants of the theorem's type under the bodies
of project definitions and every one lands in `Model.lean`.

The upper bound is existential — *some* algorithm is online, feasible and
`(2k+2)`-competitive — so it says nothing about *which*. For that, read
`Algorithm.lean` too. The lower bound and the `k+1`-page bound name
`FIFO.schedule δ` outright, so checking them means reading `Algorithm.lean` in
any case.

## Layout

| path | contents |
| --- | --- |
| `PagingWithDelay.lean` | the theorem |
| `Model.lean` | trusted definitions: problem, schedules, cost, feasibility, onlineness |
| `Algorithm.lean` | the FIFO event loop, parametric in `δ`; threshold-one FIFO is `FIFO.schedule 1` |
| `Online.lean`, `OnlineExamples.lean` | equivalent form of `Algorithm.Online`, and witnesses that it is neither vacuously true nor false |
| `EventLoop/` | invariants of `FIFO.run`; no dependency on `Competitive/` |
| `Competitive/` | cost accounting `ALG = (1+δ)M`, the charging argument, the final arithmetic |
| `FIFOFeasible.lean`, `FIFOOnline.lean` | the two non-competitive facts about FIFO, for every `δ` |
| `LowerBound/` | the tightness construction: the instance, the replay of FIFO on it, the comparator |
| `Analysis/` | generic online-analysis machinery: potential arguments, accrued delay, cache traces, FIFO ranks; no dependency on this paper's algorithm |
| `KPlusOne/` | the `k+1`-page bound: the run structure it needs, the comparator's hole, the interval inequality, the summation |

## Proof principle

Properties of FIFO are never introduced by definition or assumed as hypotheses.
Termination, threshold attainment, per-payment cost, the cache invariant,
feasibility and onlineness are all derived from `Algorithm.lean`. Proof-local
records such as `ClassCTickWitness` are *constructed* from the run, never given.

## Modelling remarks

Three places where the Lean is not a literal transcription of the TeX; none
weakens the result.

**Requests arrive in nondecreasing order** (`Instance.Chronological`). A
normalization — costs do not depend on presentation order — but load-bearing:
it puts every recorded payment before every future arrival, hence a served
request's arrival inside `W_i` rather than merely in `[0, t_i]`, and it makes
`Instance.upTo` a prefix, which onlineness needs.

**The comparator evicts only at its own fetch events.** Postponing a paper-style
solution's evictions to its next fetch stays feasible (capacity is checked only
at events) and costs no more (same fetch count; the cache is pointwise a
superset, so `delay_mono` gives no extra delay). The quantified comparators
therefore include one at least as cheap as `OPT`.

**Ties are broken explicitly**, an event loop having no infinitesimal
perturbation available: arrivals at `t` precede payments at `t`; among pages
crossing together, the one whose first pending request came earliest pays first;
simultaneous arrivals follow list order. By `delay_zero` an arrival adds nothing
at its own instant, so letting arrivals win cannot push a page over `δ`.

## Correspondence with the TeX

| TeX | Lean |
| --- | --- |
| the event loop terminates (implicit) | `run_initial_finished`, by the potential `2·\|unseen\| + \|pending\|` — the fuel bound is proved sufficient, not assumed |
| the algorithm is online (implicit) | `FIFO.schedule_online` |
| the output is a legal solution (implicit) | `FIFO.schedule_feasible` |
| `F_v(t_i) = 1` at a payment | `final_thresholdPayments` at `δ = 1` (in general `= δ`), from `value_at_sInf_first_crossing` and `BelowThreshold` |
| Lemma "cost of the algorithm", `ALG = 2M` | `FIFO.algorithmCostClaim` at `δ = 1` |
| Lemma "cache invariant" | `recentPages_eq_lastPaymentPages` with `FreshPayments` |
| Corollary "eviction time", `i ≥ j+k+1` | `samePage_spacing`, `evictionIndex_eq_previous_add_cacheSize` |
| Lemma "payment windows" (i), (ii), (iii) | `servedOccurrence_mem_paymentWindow`, `paymentBatch_delayCost_eq_one`, `auxiliaryIntervals_disjoint` (`W_i ⊆ I_i` is `paymentWindow_subset_auxiliary`) |
| Lemmas `\|A\|+\|B\| ≤ S`, `(k+1)\|C\| ≤ kM`, `\|D\| ≤ D` | `classA_classB_bound`, `classC_bound`, `classD_bound` |
| Theorem `ALG ≤ (2k+2) OPT` | `PagingWithDelay.paging_with_delay_upper_bound` |
| Section 5, `k·δ = k+1` at `δ = (k+1)/k` | `Setup.cacheSize_mul_threshold` |
| Section 5, "`p` is the unique page outside FIFO's cache" | `Setup.eq_pageAt_of_not_mem_queue` |
| Section 5, "`p` is exactly the page evicted in payment `i-1`" | `Setup.pageAt_previous`, `Setup.served_arrival_gt` |
| Section 5, `∑ Δ_i OPT ≤ OPT` | `Analysis.sum_delayIncrement_le` with `sum_intervalCost_le` |
| Section 5, `ΔP_FIFO = -m + k·1` (the rank shift) | `Analysis.rank_shift`, `Analysis.rank_append_self` |
| Section 5, the three cases of `k·Δ_i OPT + P_i - P_{i-1} ≥ 1` | `KPlusOne.interval_bound` |
| Section 5, summation `M - h ≤ k·OPT + K` | `Analysis.potential_argument`, `KPlusOne.count_le` |
| Theorem 5.1, `ALG ≤ (2k+1) OPT + c(k)` | `PagingWithDelay.paging_with_delay_upper_bound_k_plus_one_pages` |

Two places where the Lean is more careful than the prose. The paper asserts the
`OPT` residency relevant to a non-`A`, non-`D` payment is unique; the Lean proof
never needs uniqueness, and separately proves the fallback branch of
`paymentClass` unreachable (`classC_previousTime_exists`). And class-C ticks use
`comparatorCacheAt`, the cache after *all* comparator events stamped `t`,
deliberately distinct from the strict `cacheBefore` of arrival hits, because
class C permits `f = t_{p_i}`.

## The three FIFO theorems

**`ALG = (1+δ)M`** (`Competitive/AlgorithmCost.lean`) comes from the *public*
schedule semantics, not from a postulate: fetch count equals payment count, and
`totalDelay` is regrouped over a proved partition of the input occurrences into
cache hits (cost zero) and served batches, each worth exactly `δ` by
`final_thresholdPayments`.

**Feasibility** (`FIFOFeasible.lean`). Without it the bound would constrain a
cost expression without asserting the trace is admissible, `Schedule.Feasible`
being otherwise only a hypothesis on the comparator. `chronological` comes from
payment chronology; `validTransitions` from `FreshPayments`, whose content — a
payment's page is *absent* from the queue it replaces — is what makes
`cacheAfter \ previous = {fetched}` rather than `⊆`; `capacity` from
`recentPages_length`; `eventuallyServed` from the hit/batch partition above.

**Onlineness** (`FIFOOnline.lean`). `Algorithm.online_of_upTo_eq` reduces the
goal to comparing an instance with its own truncation. Three obstacles:
different fuel, removed by `run_eq_of_le` (fuel past termination is inert);
different instances, removed by `run_congr` (`step` reads its instance only
through `cacheSize`); different `unseen` lists, handled by
`filter_eq_take_of_chronological`. What remains is `mirror_earlyPayments`: while
the shared prefix lasts both states pick the same action, `nextPayment?` reading
only `now` and `pending`; once it is exhausted either a payment is due by `t`
and both must take it, every remaining arrival being later, or
`no_early_payments` shows neither run contributes anything before `t`.

Neither of the last two inspects `δ`: a payment is legal wherever it happens,
and the simulation only needs both runs to use the *same* threshold.

## Lower bound

`paging_with_delay_lower_bound` says that for every threshold `δ > 0`, cache
size `k ≥ 1` and page type with at least `k+2` pages, no ratio below `2k+2`
holds for FIFO with threshold `δ`, with any additive constant. `δ = 0` is
excluded: there the threshold is met on arrival, so FIFO pays in arrival order
and the timing of the construction stops describing the run. The comparator is
exhibited feasible, so its cost bounds `OPT` from above and the claim is about
the optimum. It is asymptotic — the additive constant pays for reaching, from
the empty cache the model starts in, the initial position the TeX assumes.

The construction of "Tightness of the analysis" is written out in
`LowerBound/Construction.lean`: `runs` runs of `2k+2` requests on `k+2` pages,
in criticality order `c, a, v_{k-1}, …, v₁, b, c, v_{k-1}, …, v₁` with `b` and
`c` exchanged between runs. Every `k+1` consecutive requests are on distinct
pages, so FIFO faults on all of them. Times are laid out in quarters
(`arrivalQuarters`): each request arrives half a unit before it reaches the
threshold, so arrivals and payments alternate — except the repeat request on
`c`, which is issued before the request on `b` it follows, which is what lets
the comparator serve both with one fetch. `LowerBound/Curve.lean` supplies the
delay curves: linear up to `δ` at the prescribed wait, then flat until a
breakpoint past the end of the instance, then growing. The growth exists only
because `delay_unbounded` forbids an eventually constant curve; since it starts
after everything either algorithm does, its slope is irrelevant and the
comparator pays exactly `δ` for each request it leaves pending.

`LowerBound.paymentCount_eq` — FIFO fetches on every request — is proved by
replaying the event loop. `LowerBound/Codes.lean` names the page fetched at
each criticality position and proves that any `k+1` consecutive fetches are on
distinct pages; `LowerBound/FIFORun.lean` walks `FIFO.run` from one *settled*
state to the next (`i` requests arrived, `i` fetches made, nothing pending) in
two steps per request, and in four at the transposed pair of each run, where
two arrivals precede the two fetches they cause. The cost of FIFO then follows
from `FIFO.algorithmCostClaim` (`algorithmCost_eq`).

`LowerBound.exists_comparator` — the paper's offline solution — is the explicit
schedule of `LowerBound/CompSchedule.lean`: `k-1` fetches installing
`v₁ … v_{k-1}`, then `runs + 1` fetches alternating between `b` and `c` (the
first of which is the initial fetch of `c`), then one fetch of `a`. Between two
of the alternating fetches its cache is the closed form
`heldCache (swapBC r 2)`, which is what makes every request but the one on `a`
a hit or served by the fetch happening at its own arrival;
`LowerBound/CompCost.lean` does that case analysis and sums, giving cost
exactly `(1+δ)·runs + (k+1)`.

The instance itself is well-formed (`input_valid`), and the final arithmetic is
`competitive_ratio_lower_bound`.

## Sanity checks

`Schedule.Feasible` is satisfiable (a one-request instance has an explicit
feasible comparator of cost `1`) and not trivial (the empty schedule, of
`totalCost` `0`, fails `eventuallyServed`). `Algorithm.Online` likewise has
witnesses on both sides in `OnlineExamples.lean`.

## `k+1` pages

`paging_with_delay_upper_bound_k_plus_one_pages` is Theorem 5.1: for `k ≥ 1`,
a cache of size `k`, and requests drawn from a universe `pages` of exactly
`k+1` pages, FIFO with threshold `(k+1)/k` satisfies

```text
ALG ≤ (2k+1)·cost(comparator) + (2k+1)(k+1)(k+2)/(2k)
```

for every feasible comparator, and is online and feasible. `KPlusOne.Setup`
bundles those hypotheses; everything downstream is stated relative to one.

**The run structure** (`KPlusOne/Window.lean`). Once `k` payments have
happened the cache is the window of the last `k` fetched pages
(`queue_eq_drop`, from `recentPages_eq_lastPaymentPages`), they are pairwise
distinct (`queue_nodup`, from `samePage_spacing`), and they are pages of the
universe (`pageAt_mem_pages`: a batch is nonempty because its delay is `δ > 0`,
and its occurrences are authentic requests). With `|pages| = k+1` this forces
`eq_pageAt_of_not_mem_queue` — *the* missing page is the one being fetched —
and `pageAt_previous`: payment `i` re-fetches the page of payment `i-k-1`,
which is what makes `final_validBatchLowerBounds` place every request of the
batch after `t_{i-1}` (`served_arrival_gt`). This is the paper's `h = k+1`:
the bookkeeping starts only once a payment has an eviction behind it.

**The comparator's hole** (`KPlusOne/Hole.lean`). The paper's potential
`∑_{q ∈ FIFO ∩ OPT} rank q` is, on `k+1` pages, `k(k+1)/2` minus the rank of
the one page the comparator is missing. `hole` names such a page after each
comparator event and moves only when that page is fetched, so the potential
becomes a single rank and the interval inequality becomes rank arithmetic.

Choosing a missing page rather than reading the comparator's cache is also
what makes the argument hold for *every* feasible comparator, including one
that evicts several pages at one fetch: the hole moves at most once per event
by construction, so no laziness normalization is needed.

**The interval** (`KPlusOne/Interval.lean`). `interval_bound` is
`1 + Φ(i+1) ≤ k·Δ_i + Φ i` with `Φ = rank (hole)`, in the paper's three cases.
The delay case is the only semantic one: if the hole stays on the fetched page
for the whole interval then the comparator holds neither the page nor a
service candidate for the batch (`no_early_service`, which reads
`serviceCandidates` — an arrival hit needs the page in `cacheBefore`, a fetch
of it needs an event), so the batch accrues its full `δ` inside the interval
(`threshold_le_delayIncrement`), and `k·δ = k+1` closes it.

**The summation** (`KPlusOne/Final.lean`). `count_le` is
`M ≤ k·OPT + 2k+1`: the potential argument over `Ico k (M-1)`, the potential
bounded by `k` at both ends, and the comparator's per-interval costs telescoping
into its fetch count and total delay. `competitive` multiplies by
`1 + δ = (2k+1)/k`; the constant it produces, `(2k+1)²/k`, is at most the
paper's `(2k+1)(k+1)(k+2)/(2k)`, which is what the theorem states.

## Reusable online-analysis machinery

`Analysis/` is written to be independent of the algorithm: it mentions FIFO,
payments and thresholds nowhere. `Amortized`, `Prefix` and `Rank` do not even
mention the model; `CacheTrace` and `Accrual` speak about an arbitrary
`Schedule`. The `k+1`-page proof is their only current client.

| file | contents |
| --- | --- |
| `Analysis/Amortized.lean` | the potential-function argument `potential_argument`: a per-step `1 + Φ(i+1) ≤ c·Δ i + Φ i` over a range bounds the number of steps by `c·∑Δ` plus the potential drop; with the telescoping lemmas `sum_Ico_increment` (`ℝ≥0`) and `sum_Ico_increment_nat` |
| `Analysis/Accrual.lean` | delay-with-service accounting: `accruedCost` is what a schedule has accrued on a request by time `t`, monotone in `t` and bounded by the delay it is finally charged, so increments over a chain of times sum to at most the total delay (`sum_delayIncrement_le`) |
| `Analysis/CacheTrace.lean` | reading a cache trace by event index instead of time: `cacheAfterCount`, `eventCount`, and their agreement with `cacheBefore` for a chronological trace |
| `Analysis/Prefix.lean` | pure list lemmas: in a list sorted by a monotone key, the elements passing a deadline are an initial segment (`filter_eq_take_countP`, `lt_countP_iff`) |
| `Analysis/Rank.lean` | FIFO ranks: `rank`, and the arithmetic of one replacement, `rank_shift` — every surviving page loses exactly one rank |

`Analysis/Prefix.lean` also generalizes the private
`filter_eq_take_of_chronological` of `FIFOOnline.lean`, which is the same
statement for request lists; the existing proof was left alone rather than
retrofitted.
