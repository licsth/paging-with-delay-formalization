import PagingWithDelay

/-!
# The public statements say what their earlier phrasings said

Two of the public theorems were rephrased to restrict the page universe. They state that
restriction as a bound on `Instance.pageUniverse`, the set of pages an input
initially caches or requests, where earlier they carried a `Finset Page` of
size `k + 1` together with the hypothesis that every request lies in it.
Feasibility of an algorithm is now part of `Algorithm` itself, and the
conditions on an input part of `Instance`.

The examples below derive the earlier phrasings from the current ones, so these
changes are changes of phrasing only, and check that the hypotheses on an
algorithm are satisfiable at all.  The last example specialises the deadline
lower bound to algorithms that never miss a deadline, where both costs are
fetch counts. Like `Checks/OnlineExamples.lean`, this file is a
check on the statements rather than part of the development; build it with
`lake build Checks`.
-/

namespace PagingWithDelay

/-- The `k+1`-page upper bound still covers every input drawn from a named
universe of exactly `k + 1` pages — initial cache and requests alike. -/
example {Page : Type*} [DecidableEq Page] {k : ℕ} (hk : 0 < k) :
    ∃ (algorithm : Algorithm Page), Algorithm.Online algorithm ∧
      ∀ (input : Instance Page) (pages : Finset Page),
        input.cacheSize = k → pages.card = k + 1 →
        (∀ page ∈ input.initialCache, page ∈ pages) →
        (∀ request ∈ input.requests, request.page ∈ pages) →
          (algorithm input).Feasible input ∧
            ∀ comparator : Schedule Page, comparator.Feasible input →
              (algorithm input).totalCost input ≤
                (2 * k + 1 : ℕ) * comparator.totalCost input := by
  obtain ⟨algorithm, _nonclairvoyant, online, competitive⟩ :=
    paging_with_delay_upper_bound_k_plus_one_pages (Page := Page) hk
  refine ⟨algorithm, online, fun input pages hsize hcard hinitial hrequests => ?_⟩
  exact ⟨algorithm.feasible input,
    competitive input hsize ((Instance.card_pageUniverse_le hinitial hrequests).trans_eq hcard)⟩

/-- The general lower bound still produces an input drawn from a universe of
exactly `k + 1` pages. -/
example {Page : Type*} [DecidableEq Page] {k : ℕ} (hk : 0 < k) (pages : Fin (k + 1) ↪ Page)
    (algorithm : Algorithm Page) (online : Algorithm.Online algorithm)
    (ratio additive : Cost) (hratio : ratio < (2 * k + 1 : ℕ)) :
    ∃ (input : Instance Page) (comparator : Schedule Page),
      input.cacheSize = k ∧
      (∃ cover : Finset Page, cover.card = k + 1 ∧
        (∀ page ∈ input.initialCache, page ∈ cover) ∧
        ∀ request ∈ input.requests, request.page ∈ cover) ∧
      comparator.Feasible input ∧
        ratio * comparator.totalCost input + additive <
          (algorithm input).totalCost input := by
  obtain ⟨input, comparator, hsize, huniverse, hfeasible, hcost⟩ :=
    paging_with_delay_general_lower_bound hk pages algorithm online ratio additive hratio
  exact ⟨input, comparator, hsize, input.exists_universe_card_eq pages huniverse,
    hfeasible, hcost⟩

/-- The hypothesis the general lower bound puts on an algorithm is satisfiable:
FIFO with threshold `1` is online, and indeed nonclairvoyant. -/
example {Page : Type*} [DecidableEq Page] :
    Algorithm.Nonclairvoyant (FIFO.algorithm (Page := Page) 1) ∧
      Algorithm.Online (FIFO.algorithm (Page := Page) 1) :=
  ⟨FIFO.algorithm_nonclairvoyant 1, FIFO.algorithm_online 1⟩

/-- The general lower bound applies to nonclairvoyant algorithms as it stands:
a nonclairvoyant algorithm is online. -/
example {Page : Type*} [DecidableEq Page] {k : ℕ} (hk : 0 < k) (pages : Fin (k + 1) ↪ Page)
    (algorithm : Algorithm Page) (nonclairvoyant : Algorithm.Nonclairvoyant algorithm)
    (ratio additive : Cost) (hratio : ratio < (2 * k + 1 : ℕ)) :
    ∃ (input : Instance Page) (comparator : Schedule Page),
      input.cacheSize = k ∧
      input.pageUniverse.card ≤ k + 1 ∧
      comparator.Feasible input ∧
        ratio * comparator.totalCost input + additive <
          (algorithm input).totalCost input :=
  paging_with_delay_general_lower_bound hk pages algorithm nonclairvoyant.online
    ratio additive hratio

/-- **The `k+1/2` bound covers the hard-deadline problem.**  An algorithm that
never misses a deadline is one whose schedules accrue no delay cost; its cost is
then exactly its number of fetches, and the comparator the bound produces has
the same property.  So the fifth theorem specialises to a statement about fetch
counts alone, which is what "`(k+1/2)`-competitive for paging with deadlines"
means.

The theorem it is derived from is the stronger one: there the algorithm is under
no such restriction and may miss a deadline and pay for it, while the comparator
never does. -/
example {Page : Type*} [DecidableEq Page] {k : ℕ} (hk : 1 ≤ k) (pages : Fin (k + 2) ↪ Page)
    (algorithm : Algorithm Page) (online : Algorithm.Online algorithm)
    (respectsDeadlines : ∀ (input : Instance Page),
      ∀ request ∈ input.requests, (algorithm input).requestCost request = 0)
    (ratio additive : Cost) (hratio : 2 * ratio < 2 * (k : Cost) + 1) :
    ∃ (input : Instance Page) (comparator : Schedule Page),
      input.cacheSize = k ∧
      input.pageUniverse.card ≤ k + 2 ∧
      comparator.Feasible input ∧
        ratio * (comparator.fetchCount : Cost) + additive <
          ((algorithm input).fetchCount : Cost) := by
  obtain ⟨input, comparator, hsize, huniverse, hfeasible, hdelay, hcost⟩ :=
    paging_with_delay_deadline_lower_bound hk pages algorithm online ratio additive hratio
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
  refine ⟨input, comparator, hsize, huniverse, hfeasible, ?_⟩
  rw [← hfetches comparator hdelay,
    ← hfetches _ (fun request hrequest => respectsDeadlines input request hrequest)]
  exact hcost

end PagingWithDelay
