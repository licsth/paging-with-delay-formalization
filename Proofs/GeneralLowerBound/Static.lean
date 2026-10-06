import Proofs.Analysis.CacheFill
import Proofs.LowerBound.CompCost

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

/-- Folding a trace whose events all precede `t` applies every event. -/
theorem foldl_cacheBefore_eq (events : List (FetchEvent Page)) (initial : Finset Page)
    {t : Time} (h : ∀ e ∈ events, e.time < t) :
    events.foldl (fun cache e => if e.time < t then e.cacheAfter else cache) initial =
      events.foldl (fun _ e => e.cacheAfter) initial :=
  List.foldl_ext _ _ _ fun _ e he => if_pos (h e he)

theorem staticComparator_cacheBefore (initial pages : Finset Page) (hole : Page)
    (hcard : initial.card ≤ (pages.erase hole).card)
    (terminal t : Time) (ht : 0 < t) (hle : t ≤ terminal) :
    (staticComparator initial pages hole terminal).cacheBefore t = pages.erase hole := by
  simp only [staticComparator, Schedule.cacheBefore, List.foldl_append,
    List.foldl_cons, List.foldl_nil, if_neg (not_lt.mpr hle)]
  rw [foldl_cacheBefore_eq _ _ fun e he => (Analysis.resetEvents_time _ _ e he).trans_lt ht,
    Analysis.resetEvents_fold _ _ hcard]

/-- The initial cache of an instance has at most `cacheSize` pages. -/
theorem initialCache_card_le (input : Instance Page) :
    input.initialCache.toFinset.card ≤ input.cacheSize :=
  (List.toFinset_card_le _).trans input.initialCache_full.le

theorem initialCache_card_le_erase (input : Instance Page) {pages : Finset Page}
    (hcard : pages.card = input.cacheSize + 1) {hole : Page} (hhole : hole ∈ pages) :
    input.initialCache.toFinset.card ≤ (pages.erase hole).card := by
  rw [Finset.card_erase_of_mem hhole, hcard, Nat.add_sub_cancel]
  exact initialCache_card_le input

/-- The static strategy serves requests on its hole at the terminal time and
all others at arrival. -/
theorem staticComparator_mem_serviceCandidates (initial pages : Finset Page) (hole : Page)
    (hcard : initial.card ≤ (pages.erase hole).card) (terminal : Time) (request : Request Page)
    (hpage : request.page ∈ pages) (harrival : 0 < request.arrival)
    (hterminal : request.arrival ≤ terminal) :
    (if request.page = hole then terminal else request.arrival) ∈
      (staticComparator initial pages hole terminal).serviceCandidates request := by
  split_ifs with hp
  · exact LowerBound.mem_serviceCandidates_of_fetch _ _ (event := ⟨terminal, hole, {hole}⟩)
      (by simp [staticComparator]) hterminal hp
  · apply LowerBound.arrival_mem_serviceCandidates_of_hit
    rw [staticComparator_cacheBefore _ _ _ hcard _ _ harrival hterminal]
    exact Finset.mem_erase.mpr ⟨hp, hpage⟩

theorem staticComparator_feasible (input : Instance Page)
    (pages : Finset Page) (hole : Page) (hhole : hole ∈ pages)
    (hcard : pages.card = input.cacheSize + 1) (terminal : Time)
    (hrequests : ∀ r ∈ input.requests, r.page ∈ pages ∧ 0 < r.arrival ∧ r.arrival ≤ terminal) :
    (staticComparator input.initialCache.toFinset pages hole terminal).Feasible input := by
  have hinit := initialCache_card_le_erase input hcard hhole
  refine ⟨rfl, List.pairwise_append.mpr ⟨?_, by simp, ?_⟩, ?_, ?_, fun r hr => ⟨_,
    staticComparator_mem_serviceCandidates _ _ _ hinit _ r (hrequests r hr).1 (hrequests r hr).2.1
      (hrequests r hr).2.2⟩⟩
  · exact List.pairwise_of_forall_mem_list fun a ha b hb => by
      rw [Analysis.resetEvents_time _ _ a ha, Analysis.resetEvents_time _ _ b hb]
  · intro a ha b hb
    rw [List.mem_singleton.mp hb, Analysis.resetEvents_time _ _ a ha]
    exact zero_le _
  · apply Analysis.validTransitions_append _ _ _ (Analysis.resetEvents_valid _ _)
    dsimp only [staticComparator]
    rw [Analysis.resetEvents_fold _ _ hinit]
    simp [Schedule.ValidTransitionsFrom]
  · intro event he
    rcases List.mem_append.mp he with he | he
    · have h := Finset.card_le_card (Analysis.resetEvents_cache_subset _ _ event he)
      rw [Finset.card_erase_of_mem hhole, hcard] at h
      simpa using h
    · simpa [List.mem_singleton.mp he] using input.positiveCapacity

theorem staticComparator_fetchCount_le (initial pages : Finset Page) (hole : Page)
    (hhole : hole ∈ pages) (terminal : Time) :
    (staticComparator initial pages hole terminal).fetchCount ≤ pages.card := by
  have := Analysis.resetEvents_length_le initial (pages.erase hole)
  rw [Finset.card_erase_of_mem hhole] at this
  have := Finset.card_pos.mpr ⟨hole, hhole⟩
  simp only [Schedule.fetchCount, staticComparator, List.length_append, List.length_singleton]
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
  refine (requestCost_le_candidate _ _ _ (staticComparator_mem_serviceCandidates _ _ _ hcard _ _
    hpage harrival hterminal)).trans ?_
  split_ifs <;> simp [request.delay_zero]

/-- Summing the static strategies counts each request's terminal delay only
once. Installing the caches contributes at most `pages.card²` fetches in
total. -/
theorem sum_staticComparator_cost_le (input : Instance Page)
    (pages : Finset Page) (hcard : pages.card = input.cacheSize + 1)
    (terminal : Time)
    (hrequests : ∀ r ∈ input.requests, r.page ∈ pages ∧ 0 < r.arrival ∧ r.arrival ≤ terminal) :
    (∑ hole ∈ pages,
        (staticComparator input.initialCache.toFinset pages hole terminal).totalCost input) ≤
      (pages.card : Cost) * pages.card +
        (input.requests.map (fun r => r.delay (terminal - r.arrival))).sum := by
  have hswap (requests : List (Request Page)) :
      (∑ hole ∈ pages, (requests.map
        (staticComparator input.initialCache.toFinset pages hole terminal).requestCost).sum) =
      (requests.map fun r => ∑ hole ∈ pages,
        (staticComparator input.initialCache.toFinset pages hole terminal).requestCost r).sum := by
    induction requests <;> simp [Finset.sum_add_distrib, *]
  simp only [Schedule.totalCost, Schedule.totalDelay, Finset.sum_add_distrib, hswap]
  refine add_le_add ?_ (List.sum_le_sum fun r hr => ?_)
  · calc _ ≤ ∑ _hole ∈ pages, (pages.card : Cost) := Finset.sum_le_sum fun hole hhole => by
          exact_mod_cast staticComparator_fetchCount_le _ _ _ hhole _
      _ = _ := by simp [nsmul_eq_mul]
  · obtain ⟨hpage, harrival, hterminal⟩ := hrequests r hr
    refine (Finset.sum_le_sum fun hole hhole => staticComparator_requestCost_le _ _ _
      (initialCache_card_le_erase input hcard hhole) _ r hpage harrival hterminal).trans_eq ?_
    simp [hpage]

end
end PagingWithDelay.GeneralLowerBound
