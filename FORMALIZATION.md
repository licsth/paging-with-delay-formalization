# Lean formalization of `fifo-upper-bound.tex`

Threshold-one FIFO is an online, feasible, `(2k+2)`-competitive algorithm for
paging with delay, and no threshold does better. Build with `lake build`.
The upper bound is complete; the lower bound ("Tightness of the analysis") is
in progress — see [Lower bound](#lower-bound).

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
`paging_with_delay_upper_bound` is about `FIFO.schedule 1`.

## Status

The build succeeds. There is no added `axiom`, no `native_decide`, no `unsafe`,
no `sorry`, and `#print axioms` reports only `propext`, `Classical.choice`,
`Quot.sound` for both `paging_with_delay_upper_bound` and
`paging_with_delay_lower_bound`.

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
`Algorithm.lean` too. The lower bound names `FIFO.schedule δ` outright, so
checking it means reading `Algorithm.lean` in any case.

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
