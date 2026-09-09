import PagingWithDelay.GeneralLowerBound.Comparators
import PagingWithDelay.GeneralLowerBound.Phases
import PagingWithDelay.PageUniverse

/-!
# The general lower bound

Running the phases of `Phases.lean` `n` times produces an input on `k+1` pages
on which the online algorithm fetches at least `n` times and whose terminal
delay is within `(1+ε)` of the algorithm's own delay, up to an additive `1`.
The `2k+1` comparators of `Comparators.lean` then cost at most `(1+ε)` times
the algorithm's cost plus a constant depending only on `k`, and averaging over
them refutes every competitive ratio below `2k+1`.
-/

namespace PagingWithDelay.GeneralLowerBound

open scoped BigOperators

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- Iterating the phase construction. -/
theorem exists_run {algorithm : Algorithm Page} (online : algorithm.Online)
    (feasible : algorithm.Feasible)
    {k : ℕ} (hk : 0 < k) {pages : Finset Page} (hcard : pages.card = k + 1)
    {c ε : Cost} (hc : ε + 1 ≤ ε * c) (n : ℕ) :
    ∃ run : AdversaryRun algorithm k pages c ε, n ≤ run.input.requests.length := by
  induction n with
  | zero => exact ⟨AdversaryRun.initial algorithm hk pages c ε, Nat.zero_le _⟩
  | succ n ih =>
      obtain ⟨run, hrun⟩ := ih
      obtain ⟨next, hnext⟩ := AdversaryRun.exists_advance online feasible hcard hc run
      exact ⟨next, by omega⟩

/-- The adaptive input of the general lower bound: arbitrarily many requests on
`k+1` pages, each one a miss, and a terminal delay close to the algorithm's
own delay. -/
theorem exists_adaptive_input {algorithm : Algorithm Page} (online : algorithm.Online)
    (feasible : algorithm.Feasible)
    {k : ℕ} (hk : 0 < k) {pages : Finset Page} (hcard : pages.card = k + 1)
    {ε : Cost} (hε : 0 < ε) (n : ℕ) :
    ∃ (input : Instance Page) (valid : input.Valid) (terminal : Time),
      input.cacheSize = k ∧
      (∀ r ∈ input.requests, r.page ∈ pages ∧ 0 < r.arrival ∧ r.arrival ≤ terminal) ∧
      input.requests.Pairwise (fun a b => a.arrival < b.arrival) ∧
      n ≤ input.requests.length ∧
      input.requests.length ≤ (algorithm input valid).fetchCount ∧
      (input.requests.map fun r => r.delay (terminal - r.arrival)).sum ≤
        (1 + ε) * (algorithm input valid).totalDelay input + 1 := by
  obtain ⟨c, _, hc⟩ := Analysis.exists_rate_growth ε hε
  obtain ⟨run, hlen⟩ := exists_run online feasible hk hcard hc n
  refine ⟨run.input, run.valid, run.now, run.size,
    fun r hr => ⟨run.memPages r hr, run.positive r hr, run.arrivalLe r hr⟩,
    run.strict, hlen, run.fetches.trans (List.length_filter_le _ _), run.delayBound.trans ?_⟩
  gcongr
  exact le_self_add.trans run.budgetTotal

/-- **The general lower bound.**  No feasible online algorithm for paging with
delay is `(2k+1-ε)`-competitive, even on a universe of exactly `k+1` pages and
with an arbitrary additive constant. -/
theorem competitive_ratio_lower_bound {algorithm : Algorithm Page} (online : algorithm.Online)
    (feasible : algorithm.Feasible)
    {k : ℕ} (hk : 0 < k) (pages : Finset Page) (hcard : pages.card = k + 1)
    (ratio additive : Cost) (hratio : ratio < (2 * k + 1 : ℕ)) :
    ∃ (input : Instance Page) (valid : input.Valid) (comparator : Schedule Page),
      input.cacheSize = k ∧
      (∀ request ∈ input.requests, request.page ∈ pages) ∧
      comparator.Feasible input ∧
        ratio * comparator.totalCost input + additive <
          (algorithm input valid).totalCost input := by
  apply competitive_ratio_lower_bound_of_families algorithm k pages ratio additive hratio
  intro ε hε
  refine ⟨(k : Cost) * k + ((k : Cost) + 1) * ((k : Cost) + 1) + 1, ?_⟩
  intro bound
  obtain ⟨n, hn⟩ := exists_nat_gt bound
  obtain ⟨input, valid, terminal, hsize, hrequests, hstrict, hlen, hfetch, hdelay⟩ :=
    exists_adaptive_input online feasible hk hcard hε n
  obtain ⟨family, hinput, hcost⟩ :=
    exists_comparisonFamily_of_delay_bound input valid pages (by rw [hsize]; exact hcard)
      hstrict terminal hrequests (algorithm input valid) ε 1 hfetch hdelay
  have hindex : 2 * k + 1 = 2 * input.cacheSize + 1 := by rw [hsize]
  have hfeasible : ∀ j, (family.comparator j).Feasible input := by
    intro j
    have h := family.feasible j
    rw [hinput] at h
    exact h
  refine ⟨{ input := input, valid := valid
            comparator := fun i => family.comparator (finCongr hindex i)
            feasible := fun i => hfeasible (finCongr hindex i) },
    ⟨hsize, fun r hr => (hrequests r hr).1⟩, ?_, ?_⟩
  · -- the algorithm's cost exceeds any prescribed bound
    refine hn.trans_le ?_
    calc (n : Cost) ≤ (input.requests.length : Cost) := by exact_mod_cast hlen
      _ ≤ ((algorithm input valid).fetchCount : Cost) := by exact_mod_cast hfetch
      _ ≤ (algorithm input valid).totalCost input := le_self_add
  · -- the aggregate comparator cost
    show (∑ i, (family.comparator (finCongr hindex i)).totalCost input) ≤
      (1 + ε) * (algorithm input valid).totalCost input +
        ((k : Cost) * k + ((k : Cost) + 1) * ((k : Cost) + 1) + 1)
    rw [(finCongr hindex).sum_comp (fun j => (family.comparator j).totalCost input)]
    refine hcost.trans (le_of_eq ?_)
    rw [hsize, hcard]
    push_cast
    ring

/-- The lower bound as the public theorem states it: the universe restriction
is a bound on the page universe of the input the construction produces, and the
`k+1` pages it requests come from the given embedding. -/
theorem competitive_ratio_lower_bound_pageUniverse {algorithm : Algorithm Page}
    (online : algorithm.Online)
    (feasible : algorithm.Feasible)
    {k : ℕ} (hk : 0 < k) (pages : Fin (k + 1) ↪ Page)
    (ratio additive : Cost) (hratio : ratio < (2 * k + 1 : ℕ)) :
    ∃ (input : Instance Page) (valid : input.Valid) (comparator : Schedule Page),
      input.cacheSize = k ∧
      input.pageUniverse.card ≤ k + 1 ∧
      comparator.Feasible input ∧
        ratio * comparator.totalCost input + additive <
          (algorithm input valid).totalCost input := by
  obtain ⟨input, valid, comparator, hsize, hrequests, hfeasible, hcost⟩ :=
    competitive_ratio_lower_bound online feasible hk (Finset.univ.map pages) (by simp)
      ratio additive hratio
  exact ⟨input, valid, comparator, hsize,
    (Instance.card_pageUniverse_le hrequests).trans_eq (by simp), hfeasible, hcost⟩

end
end PagingWithDelay.GeneralLowerBound
