import PagingWithDelay
import Proofs.FIFO.Deadlines

/-!
# The public statements say what they should

`PagingWithDelay.lean` states its results with `Algorithm.Competitive`,
`Algorithm.StrictlyCompetitive` and `DeadlineAlgorithm.Competitive`, which
compare an algorithm with every other algorithm.  The examples below unfold
them into explicit statements about comparator schedules, so comparing with
algorithms loses nothing:

* the upper bounds hold against every feasible comparator *schedule*, and the
  `k+1`-page bound covers every input drawn from a named set of `k + 1` pages;
* instantiated with a constant ratio and a constant additive term, each lower
  bound produces an explicit input and a feasible comparator schedule beating
  them; for the deadline bound the comparator meets every deadline, and both
  costs are fetch counts;
* the hypotheses the lower bounds put on an algorithm are satisfiable: FIFO is
  online and nonclairvoyant, and with threshold `0` an online deadline
  algorithm.

Like `Checks/OnlineExamples.lean`, this file is a check on the statements
rather than part of the development; build it with `lake build Checks`.
-/

namespace PagingWithDelay

/-! ## The upper bounds, against comparator schedules -/

/-- The main upper bound holds against every feasible comparator schedule. -/
example {Page : Type*} [DecidableEq Page] :
    ∃ algorithm : Algorithm Page, algorithm.Online ∧
      ∀ (input : Instance Page) (comparator : Schedule Page), comparator.Feasible input →
        (algorithm input).totalCost input ≤
          (2 * input.cacheSize + 2) * comparator.totalCost input := by
  obtain ⟨algorithm, _nonclairvoyant, online, competitive⟩ :=
    paging_with_delay_upper_bound (Page := Page)
  exact ⟨algorithm, online, fun _ _ feasible => competitive.le_of_feasible trivial feasible⟩

/-- The `k+1`-page upper bound covers every input drawn from a named universe of
`k + 1` pages, `k` the cache size — initial cache and requests alike — against
every feasible comparator schedule. -/
example {Page : Type*} [DecidableEq Page] :
    ∃ algorithm : Algorithm Page, algorithm.Online ∧
      ∀ (input : Instance Page) (pages : Finset Page), pages.card = input.cacheSize + 1 →
        (∀ page ∈ input.initialCache, page ∈ pages) →
        (∀ request ∈ input.requests, request.page ∈ pages) →
          ∀ comparator : Schedule Page, comparator.Feasible input →
            (algorithm input).totalCost input ≤
              (2 * input.cacheSize + 1) * comparator.totalCost input := by
  obtain ⟨algorithm, _nonclairvoyant, online, competitive⟩ :=
    paging_with_delay_upper_bound_k_plus_one_pages (Page := Page)
  exact ⟨algorithm, online, fun input pages hcard hinitial hrequests _ feasible =>
    competitive.le_of_feasible
      ((Instance.card_pageUniverse_le hinitial hrequests).trans_eq hcard) feasible⟩

/-! ## The lower bounds, with explicit comparator schedules

Instantiated with a constant ratio `ratio` and a constant additive term, each
lower bound produces an input and a feasible comparator schedule on which the
algorithm costs more than `ratio` times the comparator plus that term. -/

/-- Tightness of the analysis of FIFO. -/
example {Page : Type*} [DecidableEq Page]
    {δ : Cost} (hδ : 0 < δ) {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page)
    (ratio additive : Cost) (hratio : ratio < 2 * k + 2) :
    ∃ (input : Instance Page) (comparator : Schedule Page), comparator.Feasible input ∧
      ratio * comparator.totalCost input + additive <
        (FIFO.schedule δ input).totalCost input := by
  obtain ⟨input, comparator, _, hfeasible, hcost⟩ :=
    Algorithm.exists_schedule_of_not_competitive
      (FIFO_lower_bound (ratio := fun _ => ratio) hδ hk pages hratio) fun _ => additive
  exact ⟨input, comparator, hfeasible, hcost⟩

/-- The general lower bound, on an input using at most `k + 1` pages for its
cache size `k`. -/
example {Page : Type*} [DecidableEq Page] {k : ℕ} (hk : 0 < k) (pages : Fin (k + 1) ↪ Page)
    (algorithm : Algorithm Page) (online : algorithm.Online)
    (ratio additive : Cost) (hratio : ratio < 2 * k + 1) :
    ∃ (input : Instance Page) (comparator : Schedule Page),
      input.pageUniverse.card ≤ input.cacheSize + 1 ∧ comparator.Feasible input ∧
        ratio * comparator.totalCost input + additive < (algorithm input).totalCost input :=
  Algorithm.exists_schedule_of_not_competitive
    (paging_with_delay_general_lower_bound (ratio := fun _ => ratio) hk pages online hratio)
    fun _ => additive

/-- **The `k+1/2` bound is about fetch counts.**  A deadline algorithm has no
delay cost, so the deadline lower bound produces a comparator schedule meeting
every deadline whose number of fetches, times `ratio`, plus the additive term,
is below the algorithm's number of fetches. -/
example {Page : Type*} [DecidableEq Page] {k : ℕ} (hk : 1 ≤ k) (pages : Fin (k + 2) ↪ Page)
    (algorithm : DeadlineAlgorithm Page) (online : algorithm.Online)
    (ratio additive : Cost) (hratio : 2 * ratio < 2 * k + 1) :
    ∃ (input : Instance Page) (comparator : Schedule Page),
      comparator.Feasible input ∧
      (∀ request ∈ input.requests, comparator.requestCost request = 0) ∧
        ratio * (comparator.fetchCount : Cost) + additive <
          ((algorithm input).fetchCount : Cost) := by
  obtain ⟨input, comparator, _, hfeasible, hmeets, hcost⟩ :=
    DeadlineAlgorithm.exists_schedule_of_not_competitive
      (paging_with_delay_deadline_lower_bound (ratio := fun _ => ratio) hk pages online hratio)
      fun _ => additive
  have hfetches : ∀ schedule : Schedule Page,
      (∀ request ∈ input.requests, schedule.requestCost request = 0) →
        schedule.totalCost input = (schedule.fetchCount : Cost) := by
    intro schedule hzero
    have hsum : schedule.totalDelay input = 0 := by
      refine List.sum_eq_zero ?_
      intro cost hmem
      obtain ⟨request, hrequest, rfl⟩ := List.mem_map.mp hmem
      exact hzero request hrequest
    rw [Schedule.totalCost, hsum, add_zero]
  refine ⟨input, comparator, hfeasible, hmeets, ?_⟩
  rw [← hfetches comparator hmeets, ← hfetches _ (algorithm.meetsDeadlines input)]
  exact hcost

/-! ## The hypotheses on an algorithm are satisfiable -/

/-- FIFO with threshold `1` is online, and indeed nonclairvoyant. -/
example {Page : Type*} [DecidableEq Page] :
    (FIFO.algorithm (Page := Page) fun _ => 1).Nonclairvoyant ∧
      (FIFO.algorithm (Page := Page) fun _ => 1).Online :=
  ⟨FIFO.algorithm_nonclairvoyant _, FIFO.algorithm_online _⟩

/-- FIFO with threshold `0` is an online deadline algorithm, so the deadline
lower bound is not vacuous. -/
example {Page : Type*} [DecidableEq Page] :
    (FIFO.deadlineAlgorithm (Page := Page)).Online :=
  FIFO.algorithm_online fun _ => 0

/-- The general lower bound applies to nonclairvoyant algorithms as it stands:
a nonclairvoyant algorithm is online. -/
example {Page : Type*} [DecidableEq Page] {k : ℕ} (hk : 0 < k) (pages : Fin (k + 1) ↪ Page)
    (algorithm : Algorithm Page) (nonclairvoyant : algorithm.Nonclairvoyant)
    {ratio : ℕ → Cost} (hratio : ratio k < 2 * k + 1) :
    ¬ algorithm.Competitive ratio fun input => input.pageUniverse.card ≤ input.cacheSize + 1 :=
  paging_with_delay_general_lower_bound hk pages nonclairvoyant.online hratio

end PagingWithDelay
