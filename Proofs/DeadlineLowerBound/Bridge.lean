import Proofs.DeadlineLowerBound.Certificate

/-!
# From the certificate's move lists to `Model.lean` schedules

`Offline.lean` describes offline schedules as a start configuration plus a list
of timed moves, because that is the language the deadline drafts are written
in.  Nothing may be trusted in that language.  This file discharges the
translation: `buildSchedule` turns a move list from the instance's initial
cache into a `Schedule` of `Model.lean`, and `feasible_buildSchedule` proves it
`Schedule.Feasible` for an instance whose requests the moves serve, with
`totalCost` at most the number of moves.

The delay side costs nothing: a request whose delay curve still vanishes at the
end of its window contributes `0`, whether it is served by a cache hit at
arrival or by a fetch inside the window.  That is the only property of a
"deadline-shaped" curve the offline side uses.
-/

namespace PagingWithDelay.DeadlineLowerBound

open Finset

noncomputable section

variable {Page : Type*} [DecidableEq Page]

/-! ## Two model lemmas -/

/-- Any fetch of the requested page at or after its arrival is a service
candidate. -/
theorem mem_serviceCandidates_of_mem_events (schedule : Schedule Page) (request : Request Page)
    {event : FetchEvent Page} (hevent : event ∈ schedule.events)
    (harrival : request.arrival ≤ event.time) (hpage : request.page = event.fetched) :
    event.time ∈ schedule.serviceCandidates request := by
  have htime : event.time ∈ ((schedule.events.filter fun candidate =>
      request.arrival ≤ candidate.time ∧ request.page = candidate.fetched).map
        FetchEvent.time).toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨event, by simp [hevent, harrival, hpage], rfl⟩)
  unfold Schedule.serviceCandidates
  split
  · exact Finset.mem_insert_of_mem htime
  · exact htime

/-- A service candidate bounds the delay cost. -/
theorem requestCost_le_of_mem_serviceCandidates (schedule : Schedule Page)
    (request : Request Page) {time : Time}
    (hmem : time ∈ schedule.serviceCandidates request) :
    schedule.requestCost request ≤ request.delay (time - request.arrival) := by
  have hne : (schedule.serviceCandidates request).Nonempty := ⟨time, hmem⟩
  rw [Schedule.requestCost, Schedule.serviceDelay, Schedule.serviceTime, dif_pos hne]
  exact request.delay_mono (tsub_le_tsub_right (Finset.min'_le _ _ hmem) _)

/-! ## Building the schedule -/

/-- The fetch events of a move list. -/
def moveEvents : Finset Page → List (Move Page) → List (FetchEvent Page)
  | _, [] => []
  | cache, mv :: rest =>
      ⟨mv.time, mv.fetched, applyMove cache mv⟩ :: moveEvents (applyMove cache mv) rest

/-- The `Model.lean` schedule of an offline run from the start configuration. -/
def buildSchedule (start : Finset Page) (moves : List (Move Page)) : Schedule Page :=
  ⟨start, moveEvents start moves⟩

/-- The events have the times and pages of the moves. -/
theorem map_moveEvents (cache : Finset Page) (moves : List (Move Page)) :
    (moveEvents cache moves).map (fun event => (event.time, event.fetched)) =
      moves.map fun mv => (mv.time, mv.fetched) := by
  induction moves generalizing cache with
  | nil => rfl
  | cons mv rest ih => simp [moveEvents, ih]

theorem mem_moveEvents {cache : Finset Page} {moves : List (Move Page)} {mv : Move Page}
    (hmv : mv ∈ moves) :
    ∃ event ∈ moveEvents cache moves, event.time = mv.time ∧ event.fetched = mv.fetched := by
  have h := List.mem_map_of_mem (f := fun mv : Move Page => (mv.time, mv.fetched)) hmv
  rw [← map_moveEvents cache] at h
  simpa using h

/-! ## The cache before a time -/

theorem foldl_late (t : Time) :
    ∀ (cache : Finset Page) (moves : List (Move Page)) (init : Finset Page),
      (∀ mv ∈ moves, ¬ mv.time < t) →
      (moveEvents cache moves).foldl
          (fun current event => if event.time < t then event.cacheAfter else current) init = init := by
  intro cache moves
  induction moves generalizing cache with
  | nil => intro init _; rfl
  | cons mv rest ih =>
      intro init hlate
      simp only [moveEvents, List.foldl_cons, if_neg (hlate mv (List.mem_cons_self ..))]
      exact ih _ init fun candidate hcandidate =>
        hlate candidate (List.mem_cons_of_mem _ hcandidate)

/-- The translation computes the same cache as the offline model. -/
theorem cacheBefore_buildSchedule {start : Finset Page} {moves : List (Move Page)}
    (hchrono : moves.Pairwise fun earlier later => earlier.time < later.time) (t : Time) :
    (buildSchedule start moves).cacheBefore t = cacheBefore start moves t := by
  unfold Schedule.cacheBefore buildSchedule cacheBefore
  induction moves generalizing start with
  | nil => rfl
  | cons mv rest ih =>
      rw [List.pairwise_cons] at hchrono
      by_cases htime : mv.time < t
      · simpa [moveEvents, htime, cacheAfter] using ih hchrono.2
      · have hlate : ∀ candidate ∈ rest, ¬ candidate.time < t :=
          fun candidate hcandidate hlt => htime ((hchrono.1 candidate hcandidate).trans hlt)
        rw [List.filter_cons_of_neg (by simpa using htime),
          List.filter_eq_nil_iff.mpr (fun candidate hcandidate => by
            simpa using hlate candidate hcandidate)]
        simp only [moveEvents, List.foldl_cons, if_neg htime]
        exact foldl_late t _ rest start hlate

/-! ## Feasibility of the built schedule -/

theorem applyMove_sdiff {cache : Finset Page} {mv : Move Page} (hfetch : mv.fetched ∉ cache) :
    applyMove cache mv \ cache = {mv.fetched} := by
  ext y
  by_cases hy : y = mv.fetched
  · simp [applyMove, hy, hfetch]
  · simp [applyMove, hy]

theorem validTransitions_moveEvents : ∀ (cache : Finset Page) (moves : List (Move Page)),
    ValidMoves cache moves → Schedule.ValidTransitionsFrom cache (moveEvents cache moves) := by
  intro cache moves
  induction moves generalizing cache with
  | nil => intro _; trivial
  | cons mv rest ih =>
      rintro ⟨hevict, hfetch, hrest⟩
      exact ⟨Finset.mem_insert_self _ _, applyMove_sdiff hfetch, ih _ hrest⟩

theorem card_of_mem_moveEvents : ∀ (cache : Finset Page) (moves : List (Move Page)),
    ValidMoves cache moves → ∀ event ∈ moveEvents cache moves,
      event.cacheAfter.card = cache.card := by
  intro cache moves
  induction moves generalizing cache with
  | nil => intro _ _ hevent; simp [moveEvents] at hevent
  | cons mv rest ih =>
      rintro ⟨hevict, hfetch, hrest⟩ event hevent
      rw [← card_applyMove hevict hfetch]
      rcases List.mem_cons.mp hevent with rfl | hevent
      · rfl
      · exact ih _ hrest event hevent

theorem pairwise_moveEvents (cache : Finset Page) {moves : List (Move Page)}
    (hchrono : moves.Pairwise fun earlier later => earlier.time < later.time) :
    (moveEvents cache moves).Pairwise fun earlier later => earlier.time ≤ later.time := by
  have h : (moves.map fun mv => (mv.time, mv.fetched)).Pairwise fun x y => x.1 ≤ y.1 :=
    List.pairwise_map.mpr (hchrono.imp le_of_lt)
  rw [← map_moveEvents cache, List.pairwise_map] at h
  exact h

/-! ## Service -/

theorem serves_buildSchedule {start : Finset Page} {moves : List (Move Page)}
    (hchrono : moves.Pairwise fun earlier later => earlier.time < later.time)
    (request : Request Page) {deadline : Time}
    (hzero : request.delay (deadline - request.arrival) = 0)
    (hserves : Serves start moves ⟨request.page, request.arrival, deadline⟩) :
    ((buildSchedule start moves).serviceCandidates request).Nonempty ∧
      (buildSchedule start moves).requestCost request = 0 := by
  -- a service candidate at which the request has accrued no delay
  obtain ⟨time, hmem, hfree⟩ :
      ∃ time ∈ (buildSchedule start moves).serviceCandidates request, request.delay (time - request.arrival) = 0 := by
    rcases hserves with hhit | ⟨mv, hmv, hpage, hafter, hbefore⟩
    · refine ⟨request.arrival, ?_, by rw [tsub_self, request.delay_zero]⟩
      rw [Schedule.serviceCandidates, if_pos (by rwa [cacheBefore_buildSchedule hchrono])]
      exact Finset.mem_insert_self _ _
    · obtain ⟨event, hevent, htime, hfetched⟩ := mem_moveEvents (cache := start) hmv
      refine ⟨event.time, mem_serviceCandidates_of_mem_events _ _ hevent (htime ▸ hafter)
        (hfetched.trans hpage).symm, le_antisymm ?_ (zero_le _)⟩
      exact hzero ▸ request.delay_mono (tsub_le_tsub_right (htime ▸ hbefore) _)
  exact ⟨⟨time, hmem⟩,
    le_antisymm ((requestCost_le_of_mem_serviceCandidates _ _ hmem).trans hfree.le) (zero_le _)⟩

/-! ## The translation theorem -/

/-- **The certificate's schedules are `Model.lean` schedules.**  A move list
from the instance's initial cache, serving every request of `input` inside its
window, becomes a feasible schedule of cost at most the number of moves, which
serves every request at *no delay cost*. -/
theorem feasible_buildSchedule {start : Finset Page} {moves : List (Move Page)}
    {input : Instance Page} (hstart : input.initialCache.toFinset = start)
    (hvalid : ValidMoves start moves)
    (hchrono : moves.Pairwise fun earlier later => earlier.time < later.time)
    (deadline : Request Page → Time)
    (hzero : ∀ request ∈ input.requests,
      request.delay (deadline request - request.arrival) = 0)
    (hserves : ∀ request ∈ input.requests,
      Serves start moves ⟨request.page, request.arrival, deadline request⟩) :
    (buildSchedule start moves).Feasible input ∧
      (buildSchedule start moves).totalCost input ≤ (moves.length : Cost) ∧
      ∀ request ∈ input.requests, (buildSchedule start moves).requestCost request = 0 := by
  have hservice := fun request hrequest =>
    serves_buildSchedule hchrono request (hzero request hrequest) (hserves request hrequest)
  have hcard : start.card ≤ input.cacheSize :=
    hstart ▸ (List.toFinset_card_le _).trans input.initialCache_full.le
  refine ⟨⟨hstart.symm, pairwise_moveEvents start hchrono,
    validTransitions_moveEvents _ _ hvalid, fun event hevent => (card_of_mem_moveEvents _ _ hvalid event hevent).trans_le hcard,
    fun request hrequest => (hservice request hrequest).1⟩, ?_,
    fun request hrequest => (hservice request hrequest).2⟩
  have hdelay : (buildSchedule start moves).totalDelay input = 0 :=
    List.sum_eq_zero fun cost hcost => by
      obtain ⟨request, hrequest, rfl⟩ := List.mem_map.mp hcost
      exact (hservice request hrequest).2
  have hlength : (moveEvents start moves).length = moves.length := by
    simpa using congrArg List.length (map_moveEvents start moves)
  rw [Schedule.totalCost, hdelay, add_zero, Schedule.fetchCount]
  exact_mod_cast hlength.le

/-! ## The certificate's bound on the optimum, in the language of `Model.lean` -/

/-- **The offline certificate, discharged into the trusted definitions.**  At
any checkpoint, the certificate yields a schedule that `Model.lean` calls
feasible for the instance it has served, of total cost at most `m + 1`, which
serves every request at no delay cost: the comparator never buys its way out of
a deadline.

This is the write-up's `OPT ≤ B + 1`.  The hypotheses are: the certificate
starts from the instance's initial cache (`hstart`), every request is free
inside its window (`hzero`), and every request of the instance is one the
certificate has served (`hmem`). -/
theorem certificate_totalCost_le {V start : Finset Page}
    {processed : List (Window Page)} {alpha : Window Page} {c : Page} {L : Finset Page}
    {q : Option Page} {m : ℕ} {now : Time}
    (hcert : Certificate V start processed alpha c L q m now)
    {z : Page} (hz : z ∈ L) (hne : (V \ {c, z}).Nonempty)
    {input : Instance Page} (deadline : Request Page → Time)
    (hstart : input.initialCache.toFinset = start)
    (hzero : ∀ request ∈ input.requests,
      request.delay (deadline request - request.arrival) = 0)
    (hmem : ∀ request ∈ input.requests,
      (⟨request.page, request.arrival, deadline request⟩ : Window Page) ∈ alpha :: processed) :
    ∃ schedule : Schedule Page, schedule.Feasible input ∧
      schedule.totalCost input ≤ ((m + 1 : ℕ) : Cost) ∧
      ∀ request ∈ input.requests, schedule.requestCost request = 0 := by
  obtain ⟨t, cfg, moves, hvalid, hchrono, _, hlength, hserves, _⟩ :=
    hcert.exists_final_schedule hz hne
  obtain ⟨hfeasible, hcost, hdelay⟩ :=
    feasible_buildSchedule hstart hvalid hchrono deadline hzero fun request hrequest => hserves _ (hmem request hrequest)
  exact ⟨_, hfeasible, hcost.trans (by exact_mod_cast hlength), hdelay⟩

end
end PagingWithDelay.DeadlineLowerBound
