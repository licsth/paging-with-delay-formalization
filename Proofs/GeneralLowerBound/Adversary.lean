import Proofs.Analysis.Adaptive
import Proofs.Analysis.GeometricDelay

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

/-- Extend an input by a cache miss and force at least one further fetch.
The algorithm may prefetch, batch events, or leave cache slots unused. -/
theorem exists_extension_more_fetches (algorithm : Algorithm Page)
    (online : algorithm.Online)
    (input : Instance Page) (pages : Finset Page)
    (hcard : pages.card = input.cacheSize + 1) :
    ∃ (request : Request Page) (hlast : ∀ r ∈ input.requests, r.arrival ≤ request.arrival),
      request.page ∈ pages ∧
      (algorithm input).fetchCount <
        (algorithm (input.appendRequest request hlast)).fetchCount := by
  let old := algorithm input
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
  have hcapacity := old.cacheBefore_card_le input (algorithm.feasible input) arrival
  have hnsubset : ¬pages ⊆ old.cacheBefore arrival := by
    intro h
    have := (Finset.card_le_card h).trans hcapacity
    omega
  obtain ⟨page, hpage, hmiss⟩ := Finset.not_subset.mp hnsubset
  let request := Analysis.linearRequest page arrival 1 zero_lt_one
  have hlast : ∀ r ∈ input.requests, r.arrival ≤ request.arrival :=
    fun r hr => (hrequest r hr).trans htime.le
  let extended := algorithm (input.appendRequest request hlast)
  have hmiss' : request.page ∉ extended.cacheBefore request.arrival := by
    rw [online.appendRequest_cacheBefore input request hlast]
    exact hmiss
  have hserved := (algorithm.feasible (input.appendRequest request hlast)).eventuallyServed
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
    rw [online.appendRequest_prefix input request hlast htime]
    apply congrArg (Schedule.mk old.initialCache)
    exact List.filter_eq_self.mpr (fun e he => by simpa using hevent e he)
  refine ⟨request, hlast, hpage, ?_⟩
  have hlength : (extended.upTo cutoff).events.length < extended.events.length := by
    apply List.length_filter_lt_length_iff_exists.mpr
    exact ⟨event, he'.1, by simpa using not_le.mpr hnew⟩
  simpa [hprefix, Schedule.fetchCount] using hlength

/-- There are inputs over the chosen universe forcing any prescribed
number of fetches, starting from any `k` of its pages. -/
theorem exists_many_fetches (algorithm : Algorithm Page) (online : algorithm.Online)
    {k : ℕ} (hk : 0 < k) (pages : Finset Page) (hcard : pages.card = k + 1)
    (n : ℕ) :
    ∃ input : Instance Page,
      input.cacheSize = k ∧
      (∀ r ∈ input.requests, r.page ∈ pages) ∧
      n ≤ (algorithm input).fetchCount := by
  induction n with
  | zero =>
      exact ⟨⟨k, pages.toList.take k, [], List.Pairwise.nil, hk,
        (Finset.nodup_toList pages).sublist (List.take_sublist _ _), by simp [hcard]⟩,
        rfl, by simp, Nat.zero_le _⟩
  | succ n ih =>
      obtain ⟨input, hsize, hpages, hn⟩ := ih
      obtain ⟨request, hlast, hp, hmore⟩ :=
        exists_extension_more_fetches algorithm online input pages
          (by simpa [hsize] using hcard)
      refine ⟨input.appendRequest request hlast, hsize, ?_, by omega⟩
      intro r hr
      simp only [Instance.appendRequest, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hpages r hr
      · exact hp

/-- Consequently no fixed additive constant bounds the cost of a feasible
online algorithm, even on a universe of exactly `k+1` pages. -/
theorem exists_large_cost (algorithm : Algorithm Page) (online : algorithm.Online)
    {k : ℕ} (hk : 0 < k) (pages : Finset Page) (hcard : pages.card = k + 1)
    (bound : Cost) :
    ∃ input : Instance Page,
      input.cacheSize = k ∧
      (∀ r ∈ input.requests, r.page ∈ pages) ∧
      bound < (algorithm input).totalCost input := by
  obtain ⟨n, hn⟩ := exists_nat_gt bound
  obtain ⟨input, hsize, hpages, hcount⟩ :=
    exists_many_fetches algorithm online hk pages hcard n
  refine ⟨input, hsize, hpages, hn.trans_le ?_⟩
  exact (Nat.cast_le.mpr hcount).trans (le_add_of_nonneg_right (zero_le _))

end
end PagingWithDelay.GeneralLowerBound
