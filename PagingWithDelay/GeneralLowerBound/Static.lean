import PagingWithDelay.Analysis.CacheFill

/-!
# The static offline strategies

For each possible hole, fill the other `k` pages at time zero and keep them
until the common terminal time, then fetch the hole. These are actual feasible
schedules in the empty-cache model, costing `k+1` fetches each. Only requests
on the designated hole can incur delay.
-/

namespace PagingWithDelay.GeneralLowerBound

open scoped BigOperators

variable {Page : Type*} [DecidableEq Page]

noncomputable section

def staticComparator (pages : Finset Page) (hole : Page) (terminal : Time) : Schedule Page :=
  ⟨Analysis.fillEvents ∅ (pages.erase hole).toList ++ [⟨terminal, hole, {hole}⟩]⟩

theorem staticComparator_cacheBefore (pages : Finset Page) (hole : Page)
    (terminal t : Time) (ht : 0 < t) (hle : t ≤ terminal) :
    (staticComparator pages hole terminal).cacheBefore t = pages.erase hole := by
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
  rw [hfill _ _ (Analysis.fillEvents_time _ _), Analysis.fillEvents_fold]
  simp

theorem staticComparator_feasible (input : Instance Page) (valid : input.Valid)
    (pages : Finset Page) (hole : Page) (hhole : hole ∈ pages)
    (hcard : pages.card = input.cacheSize + 1) (terminal : Time)
    (hrequests : ∀ r ∈ input.requests, r.page ∈ pages ∧ 0 < r.arrival ∧ r.arrival ≤ terminal) :
    (staticComparator pages hole terminal).Feasible input := by
  have hheld : (pages.erase hole).card = input.cacheSize := by
    rw [Finset.card_erase_of_mem hhole, hcard]
    omega
  constructor
  · apply List.pairwise_append.mpr
    refine ⟨?_, by simp, ?_⟩
    · apply List.pairwise_of_forall_mem_list
      intro a ha b hb
      rw [Analysis.fillEvents_time _ _ a ha, Analysis.fillEvents_time _ _ b hb]
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      rw [Analysis.fillEvents_time _ _ a ha]
      exact zero_le _
  · apply Analysis.validTransitions_append
    · exact Analysis.fillEvents_valid _ _ (Finset.nodup_toList _) (by simp)
    · rw [Analysis.fillEvents_fold]
      simp [Schedule.ValidTransitionsFrom]
  · intro event he
    rcases List.mem_append.mp he with he | he
    · have h := Finset.card_le_card (Analysis.fillEvents_cache_subset ∅
        (pages.erase hole).toList event he)
      simpa [hheld] using h
    · simp only [List.mem_singleton] at he
      subst event
      simpa using valid.positiveCapacity
  · intro r hr
    have h := hrequests r hr
    by_cases hp : r.page = hole
    · refine ⟨terminal, ?_⟩
      have hmem : terminal ∈
          (((staticComparator pages hole terminal).events.filter fun e =>
            decide (r.arrival ≤ e.time ∧ r.page = e.fetched)).map FetchEvent.time).toFinset := by
        apply List.mem_toFinset.mpr
        apply List.mem_map.mpr
        refine ⟨⟨terminal, hole, {hole}⟩, ?_, rfl⟩
        simp [staticComparator, h.2.2, hp]
      unfold Schedule.serviceCandidates
      split
      · exact Finset.mem_insert_of_mem hmem
      · exact hmem
    · have hhit : r.page ∈ (staticComparator pages hole terminal).cacheBefore r.arrival := by
        rw [staticComparator_cacheBefore _ _ _ _ h.2.1 h.2.2]
        exact Finset.mem_erase.mpr ⟨hp, h.1⟩
      exact ⟨r.arrival, by simp [Schedule.serviceCandidates, hhit]⟩

theorem staticComparator_fetchCount (pages : Finset Page) (hole : Page)
    (hhole : hole ∈ pages) (terminal : Time) :
    (staticComparator pages hole terminal).fetchCount = pages.card := by
  simp only [Schedule.fetchCount, staticComparator, List.length_append,
    Analysis.fillEvents_length, Finset.length_toList, List.length_singleton,
    Finset.card_erase_of_mem hhole]
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
theorem staticComparator_requestCost_le (pages : Finset Page) (hole : Page)
    (terminal : Time) (request : Request Page)
    (hpage : request.page ∈ pages) (harrival : 0 < request.arrival)
    (hterminal : request.arrival ≤ terminal) :
    (staticComparator pages hole terminal).requestCost request ≤
      if request.page = hole then request.delay (terminal - request.arrival) else 0 := by
  by_cases hp : request.page = hole
  · rw [if_pos hp]
    apply requestCost_le_candidate
    have hmem : terminal ∈
        (((staticComparator pages hole terminal).events.filter fun e =>
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
        (staticComparator pages hole terminal).cacheBefore request.arrival := by
      rw [staticComparator_cacheBefore _ _ _ _ harrival hterminal]
      exact Finset.mem_erase.mpr ⟨hp, hpage⟩
    have hmem : request.arrival ∈
        (staticComparator pages hole terminal).serviceCandidates request := by
      simp [Schedule.serviceCandidates, hhit]
    simpa [request.delay_zero] using requestCost_le_candidate _ request _ hmem

/-- Summing the static strategies counts each request's terminal delay only
once. The empty initial caches contribute `pages.card²` fetches in total. -/
theorem sum_staticComparator_cost_le (input : Instance Page) (pages : Finset Page)
    (terminal : Time)
    (hrequests : ∀ r ∈ input.requests, r.page ∈ pages ∧ 0 < r.arrival ∧ r.arrival ≤ terminal) :
    (∑ hole ∈ pages, (staticComparator pages hole terminal).totalCost input) ≤
      (pages.card : Cost) * pages.card +
        (input.requests.map (fun r => r.delay (terminal - r.arrival))).sum := by
  have hdelay (requests : List (Request Page))
      (hr : ∀ r ∈ requests, r.page ∈ pages ∧ 0 < r.arrival ∧ r.arrival ≤ terminal) :
      (∑ hole ∈ pages,
        (requests.map (staticComparator pages hole terminal).requestCost).sum) ≤
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
              intro hole _
              exact staticComparator_requestCost_le _ _ _ _ h.1 h.2.1 h.2.2
            _ = r.delay (terminal - r.arrival) := by simp [h.1]
        · exact ih (fun r hr' => hr r (by simp [hr']))
  simp only [Schedule.totalCost, Finset.sum_add_distrib]
  have hfetch : (∑ hole ∈ pages,
      ((staticComparator pages hole terminal).fetchCount : Cost)) =
      (pages.card : Cost) * pages.card := by
    calc
      _ = ∑ _hole ∈ pages, (pages.card : Cost) := by
        apply Finset.sum_congr rfl
        intro hole hhole
        rw [staticComparator_fetchCount _ _ hhole]
      _ = _ := by simp [nsmul_eq_mul]
  rw [hfetch]
  exact add_le_add le_rfl (hdelay input.requests hrequests)

end
end PagingWithDelay.GeneralLowerBound
