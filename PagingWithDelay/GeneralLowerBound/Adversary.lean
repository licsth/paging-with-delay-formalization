import PagingWithDelay.Analysis.Adaptive
import PagingWithDelay.Analysis.GeometricDelay

/-!
# Arbitrarily costly adaptive inputs

A feasible online algorithm can be forced to make arbitrarily many fetches
using only `k+1` pages. The next request is chosen after inspecting the run on
the current prefix. Onlineness preserves the earlier actions and the cache
before the new arrival, so requesting an absent page forces a further fetch.

This construction establishes unbounded cost, independently of any comparator
estimate. Its long gaps are not the short gaps required by the static-strategy
delay comparison in the `2k+1` argument.
-/

namespace PagingWithDelay.GeneralLowerBound

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- Extend a legal input by a cache miss and force at least one further fetch.
The algorithm may prefetch, batch events, or leave cache slots unused. -/
theorem exists_extension_more_fetches (algorithm : Algorithm Page)
    (online : algorithm.Online)
    (feasible : algorithm.Feasible)
    (input : Instance Page) (valid : input.Valid) (pages : Finset Page)
    (hcard : pages.card = input.cacheSize + 1) :
    ∃ (request : Request Page) (extendedValid : (input.appendRequest request).Valid),
      request.page ∈ pages ∧
      (algorithm input valid).fetchCount <
        (algorithm (input.appendRequest request) extendedValid).fetchCount := by
  let old := algorithm input valid
  let times := (old.events.map FetchEvent.time ++ input.requests.map Request.arrival).toFinset
  let cutoff : Time := times.sup id
  have hevent : ∀ e ∈ old.events, e.time ≤ cutoff := by
    intro e he
    apply Finset.le_sup (f := id)
    simp only [times, List.mem_toFinset, List.mem_append, List.mem_map]
    exact Or.inl ⟨e, he, rfl⟩
  have hrequest : ∀ r ∈ input.requests, r.arrival ≤ cutoff := by
    intro r hr
    apply Finset.le_sup (f := id)
    simp only [times, List.mem_toFinset, List.mem_append, List.mem_map]
    exact Or.inr ⟨r, hr, rfl⟩
  let arrival : Time := cutoff + 1
  have htime : cutoff < arrival := lt_add_of_pos_right _ zero_lt_one
  have hcapacity := old.cacheBefore_card_le input (feasible.scheduleFeasible input valid) arrival
  have hnsubset : ¬pages ⊆ old.cacheBefore arrival := by
    intro h
    have := (Finset.card_le_card h).trans hcapacity
    omega
  obtain ⟨page, hpage, hmiss⟩ := Finset.not_subset.mp hnsubset
  let request := Analysis.linearRequest page arrival 1 zero_lt_one
  have extendedValid : (input.appendRequest request).Valid :=
    valid.appendRequest request (fun r hr => (hrequest r hr).trans htime.le)
  let extended := algorithm (input.appendRequest request) extendedValid
  have hmiss' : request.page ∉ extended.cacheBefore request.arrival := by
    rw [online.appendRequest_cacheBefore input valid request extendedValid]
    exact hmiss
  have hserved := (feasible.scheduleFeasible (input.appendRequest request) extendedValid).eventuallyServed
    request (by simp [Instance.appendRequest])
  obtain ⟨service, hservice⟩ := hserved
  change service ∈ extended.serviceCandidates request at hservice
  simp only [Schedule.serviceCandidates, hmiss', if_false, List.mem_toFinset,
    List.mem_map] at hservice
  obtain ⟨event, he, _⟩ := hservice
  have he' := List.mem_filter.mp he
  have hnew : cutoff < event.time :=
    htime.trans_le (of_decide_eq_true he'.2).1
  have hprefix : extended.upTo cutoff = old := by
    rw [online.appendRequest_prefix input valid request extendedValid htime]
    apply congrArg Schedule.mk
    exact List.filter_eq_self.mpr (fun e he => by simpa using hevent e he)
  refine ⟨request, extendedValid, hpage, ?_⟩
  have hlength : (extended.upTo cutoff).events.length < extended.events.length := by
    apply List.length_filter_lt_length_iff_exists.mpr
    exact ⟨event, he'.1, by simpa using not_le.mpr hnew⟩
  simpa [hprefix, Schedule.fetchCount] using hlength

/-- There are legal inputs over the chosen universe forcing any prescribed
number of fetches. No assumption of a full initial cache is made. -/
theorem exists_many_fetches (algorithm : Algorithm Page) (online : algorithm.Online)
    (feasible : algorithm.Feasible)
    {k : ℕ} (hk : 0 < k) (pages : Finset Page) (hcard : pages.card = k + 1)
    (n : ℕ) :
    ∃ (input : Instance Page) (valid : input.Valid),
      input.cacheSize = k ∧
      (∀ r ∈ input.requests, r.page ∈ pages) ∧
      n ≤ (algorithm input valid).fetchCount := by
  induction n with
  | zero =>
      exact ⟨⟨k, []⟩, ⟨List.Pairwise.nil, hk⟩, rfl, by simp, Nat.zero_le _⟩
  | succ n ih =>
      obtain ⟨input, valid, hsize, hpages, hn⟩ := ih
      obtain ⟨request, extendedValid, hp, hmore⟩ :=
        exists_extension_more_fetches algorithm online feasible input valid pages
          (by simpa [hsize] using hcard)
      refine ⟨input.appendRequest request, extendedValid, hsize, ?_, by omega⟩
      intro r hr
      simp only [Instance.appendRequest, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hpages r hr
      · exact hp

/-- Consequently no fixed additive constant bounds the cost of a feasible
online algorithm, even on a universe of exactly `k+1` pages. -/
theorem exists_large_cost (algorithm : Algorithm Page) (online : algorithm.Online)
    (feasible : algorithm.Feasible)
    {k : ℕ} (hk : 0 < k) (pages : Finset Page) (hcard : pages.card = k + 1)
    (bound : Cost) :
    ∃ (input : Instance Page) (valid : input.Valid),
      input.cacheSize = k ∧
      (∀ r ∈ input.requests, r.page ∈ pages) ∧
      bound < (algorithm input valid).totalCost input := by
  obtain ⟨n, hn⟩ := exists_nat_gt bound
  obtain ⟨input, valid, hsize, hpages, hcount⟩ :=
    exists_many_fetches algorithm online feasible hk pages hcard n
  refine ⟨input, valid, hsize, hpages, hn.trans_le ?_⟩
  exact (Nat.cast_le.mpr hcount).trans (le_add_of_nonneg_right (zero_le _))

end
end PagingWithDelay.GeneralLowerBound
