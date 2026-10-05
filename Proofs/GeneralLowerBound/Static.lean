import Proofs.Analysis.CacheFill

/-!
# The static offline strategies

For each possible hole, install the other `k` pages at time zero — fetching
those the initial cache lacks — and keep them until the common terminal time,
then fetch the hole. These are actual feasible schedules costing at most `k+1`
fetches each. Only requests on the designated hole can incur delay.
-/

namespace PagingWithDelay.GeneralLowerBound

open scoped BigOperators

variable {Page : Type*} [DecidableEq Page]

noncomputable section

def staticComparator (initial pages : Finset Page) (hole : Page) (terminal : Time) :
    Schedule Page :=
  ⟨initial, Analysis.resetEvents initial (pages.erase hole) ++ [⟨terminal, hole, {hole}⟩]⟩

theorem staticComparator_cacheBefore (initial pages : Finset Page) (hole : Page)
    (hcard : initial.card ≤ (pages.erase hole).card)
    (terminal t : Time) (ht : 0 < t) (hle : t ≤ terminal) :
    (staticComparator initial pages hole terminal).cacheBefore t = pages.erase hole := by
  have hfill : ∀ (events : List (FetchEvent Page)) (initial : Finset Page),
      (∀ e ∈ events, e.time = 0) →
      events.foldl (fun cache e => if e.time < t then e.cacheAfter else cache) initial =
        events.foldl (fun _ e => e.cacheAfter) initial := by
    intro events initial hevents
    induction events generalizing initial with
    | nil => rfl
    | cons e rest ih =>
        simp only [List.foldl_cons, hevents e (by simp), if_pos ht]
        exact ih _ (fun e he => hevents e (by simp [he]))
  simp only [staticComparator, Schedule.cacheBefore, List.foldl_append,
    List.foldl_cons, List.foldl_nil, if_neg (not_lt.mpr hle)]
  rw [hfill _ _ (Analysis.resetEvents_time _ _), Analysis.resetEvents_fold _ _ hcard]

/-- The initial cache of a valid instance has at most `cacheSize` pages. -/
theorem initialCache_card_le (input : Instance Page) (valid : input.Valid) :
    input.initialCache.toFinset.card ≤ input.cacheSize :=
  (List.toFinset_card_le _).trans valid.initialCache_full.le

theorem staticComparator_feasible (input : Instance Page) (valid : input.Valid)
    (pages : Finset Page) (hole : Page) (hhole : hole ∈ pages)
    (hcard : pages.card = input.cacheSize + 1) (terminal : Time)
    (hrequests : ∀ r ∈ input.requests, r.page ∈ pages ∧ 0 < r.arrival ∧ r.arrival ≤ terminal) :
    (staticComparator input.initialCache.toFinset pages hole terminal).Feasible input := by
  have hheld : (pages.erase hole).card = input.cacheSize := by
    rw [Finset.card_erase_of_mem hhole, hcard]
    omega
  have hinit : input.initialCache.toFinset.card ≤ (pages.erase hole).card :=
    hheld ▸ initialCache_card_le input valid
  constructor
  · rfl
  · apply List.pairwise_append.mpr
    refine ⟨?_, by simp, ?_⟩
    · apply List.pairwise_of_forall_mem_list
      intro a ha b hb
      rw [Analysis.resetEvents_time _ _ a ha, Analysis.resetEvents_time _ _ b hb]
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      rw [Analysis.resetEvents_time _ _ a ha]
      exact zero_le _
  · apply Analysis.validTransitions_append
    · exact Analysis.resetEvents_valid _ _
    · show Schedule.ValidTransitionsFrom (List.foldl _ input.initialCache.toFinset _) _
      rw [Analysis.resetEvents_fold _ _ hinit]
      simp [Schedule.ValidTransitionsFrom]
  · intro event he
    rcases List.mem_append.mp he with he | he
    · have h := Finset.card_le_card (Analysis.resetEvents_cache_subset _
        (pages.erase hole) event he)
      simpa [hheld] using h
    · simp only [List.mem_singleton] at he
      subst event
      simpa using valid.positiveCapacity
  · intro r hr
    have h := hrequests r hr
    by_cases hp : r.page = hole
    · refine ⟨terminal, ?_⟩
      have hmem : terminal ∈
          (((staticComparator input.initialCache.toFinset pages hole terminal).events.filter
            fun e => decide (r.arrival ≤ e.time ∧ r.page = e.fetched)).map
              FetchEvent.time).toFinset := by
        apply List.mem_toFinset.mpr
        apply List.mem_map.mpr
        refine ⟨⟨terminal, hole, {hole}⟩, ?_, rfl⟩
        simp [staticComparator, h.2.2, hp]
      unfold Schedule.serviceCandidates
      split
      · exact Finset.mem_insert_of_mem hmem
      · exact hmem
    · have hhit : r.page ∈
          (staticComparator input.initialCache.toFinset pages hole terminal).cacheBefore
            r.arrival := by
        rw [staticComparator_cacheBefore _ _ _ hinit _ _ h.2.1 h.2.2]
        exact Finset.mem_erase.mpr ⟨hp, h.1⟩
      exact ⟨r.arrival, by simp [Schedule.serviceCandidates, hhit]⟩

theorem staticComparator_fetchCount_le (initial pages : Finset Page) (hole : Page)
    (hhole : hole ∈ pages) (terminal : Time) :
    (staticComparator initial pages hole terminal).fetchCount ≤ pages.card := by
  simp only [Schedule.fetchCount, staticComparator, List.length_append, List.length_singleton]
  have := Analysis.resetEvents_length_le initial (pages.erase hole)
  rw [Finset.card_erase_of_mem hhole] at this
  have := Finset.card_pos.mpr ⟨hole, hhole⟩
  omega

private theorem requestCost_le_candidate (schedule : Schedule Page) (request : Request Page)
    (t : Time) (ht : t ∈ schedule.serviceCandidates request) :
    schedule.requestCost request ≤ request.delay (t - request.arrival) := by
  have hne : (schedule.serviceCandidates request).Nonempty := ⟨t, ht⟩
  simp only [Schedule.requestCost, Schedule.serviceDelay, Schedule.serviceTime, dif_pos hne,
    Option.getD_some]
  exact request.delay_mono (tsub_le_tsub_right (Finset.min'_le _ _ ht) _)

/-- The static strategy only delays requests on its hole, and serves those no
later than the terminal time. -/
theorem staticComparator_requestCost_le (initial pages : Finset Page) (hole : Page)
    (hcard : initial.card ≤ (pages.erase hole).card)
    (terminal : Time) (request : Request Page)
    (hpage : request.page ∈ pages) (harrival : 0 < request.arrival)
    (hterminal : request.arrival ≤ terminal) :
    (staticComparator initial pages hole terminal).requestCost request ≤
      if request.page = hole then request.delay (terminal - request.arrival) else 0 := by
  by_cases hp : request.page = hole
  · rw [if_pos hp]
    apply requestCost_le_candidate
    have hmem : terminal ∈
        (((staticComparator initial pages hole terminal).events.filter fun e =>
          decide (request.arrival ≤ e.time ∧ request.page = e.fetched)).map
            FetchEvent.time).toFinset := by
      apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      refine ⟨⟨terminal, hole, {hole}⟩, ?_, rfl⟩
      simp [staticComparator, hterminal, hp]
    unfold Schedule.serviceCandidates
    split
    · exact Finset.mem_insert_of_mem hmem
    · exact hmem
  · rw [if_neg hp]
    have hhit : request.page ∈
        (staticComparator initial pages hole terminal).cacheBefore request.arrival := by
      rw [staticComparator_cacheBefore _ _ _ hcard _ _ harrival hterminal]
      exact Finset.mem_erase.mpr ⟨hp, hpage⟩
    have hmem : request.arrival ∈
        (staticComparator initial pages hole terminal).serviceCandidates request := by
      simp [Schedule.serviceCandidates, hhit]
    simpa [request.delay_zero] using requestCost_le_candidate _ request _ hmem

/-- Summing the static strategies counts each request's terminal delay only
once. Installing the caches contributes at most `pages.card²` fetches in
total. -/
theorem sum_staticComparator_cost_le (input : Instance Page) (valid : input.Valid)
    (pages : Finset Page) (hcard : pages.card = input.cacheSize + 1)
    (terminal : Time)
    (hrequests : ∀ r ∈ input.requests, r.page ∈ pages ∧ 0 < r.arrival ∧ r.arrival ≤ terminal) :
    (∑ hole ∈ pages,
        (staticComparator input.initialCache.toFinset pages hole terminal).totalCost input) ≤
      (pages.card : Cost) * pages.card +
        (input.requests.map (fun r => r.delay (terminal - r.arrival))).sum := by
  have hinit : ∀ hole ∈ pages,
      input.initialCache.toFinset.card ≤ (pages.erase hole).card := by
    intro hole hhole
    rw [Finset.card_erase_of_mem hhole, hcard, Nat.add_sub_cancel]
    exact initialCache_card_le input valid
  have hdelay (requests : List (Request Page))
      (hr : ∀ r ∈ requests, r.page ∈ pages ∧ 0 < r.arrival ∧ r.arrival ≤ terminal) :
      (∑ hole ∈ pages,
        (requests.map
          (staticComparator input.initialCache.toFinset pages hole terminal).requestCost).sum) ≤
        (requests.map (fun r => r.delay (terminal - r.arrival))).sum := by
    induction requests with
    | nil => simp
    | cons r rest ih =>
        simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
        apply add_le_add
        · have h := hr r (by simp)
          calc
            _ ≤ ∑ hole ∈ pages,
                if r.page = hole then r.delay (terminal - r.arrival) else 0 := by
              apply Finset.sum_le_sum
              intro hole hhole
              exact staticComparator_requestCost_le _ _ _ (hinit hole hhole) _ _ h.1 h.2.1 h.2.2
            _ = r.delay (terminal - r.arrival) := by simp [h.1]
        · exact ih (fun r hr' => hr r (by simp [hr']))
  simp only [Schedule.totalCost, Finset.sum_add_distrib]
  have hfetch : (∑ hole ∈ pages,
      ((staticComparator input.initialCache.toFinset pages hole terminal).fetchCount : Cost)) ≤
      (pages.card : Cost) * pages.card := by
    calc
      _ ≤ ∑ _hole ∈ pages, (pages.card : Cost) := by
        apply Finset.sum_le_sum
        intro hole hhole
        exact_mod_cast staticComparator_fetchCount_le _ _ _ hhole _
      _ = _ := by simp [nsmul_eq_mul]
  exact add_le_add hfetch (hdelay input.requests hrequests)

end
end PagingWithDelay.GeneralLowerBound
