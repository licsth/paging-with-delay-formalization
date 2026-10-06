import Proofs.Analysis.CacheFill
import Proofs.LowerBound.CompCost
import Proofs.GeneralLowerBound.Static
import Mathlib.Data.Fintype.EquivFin

/-!
# The dynamic offline family

The family has distinct holes, all different from the most recently requested
page. On a request for `q`, a strategy whose hole is `q` fetches `q` and evicts
the previous requested page. Every other strategy stays put. Thus at most one
strategy moves per request. The caches are installed at time zero, by fetching
whatever the common initial cache lacks.
-/

namespace PagingWithDelay.GeneralLowerBound

open scoped BigOperators

variable {Page : Type*} [DecidableEq Page]

noncomputable section

private theorem candidate_append (schedule : Schedule Page) (event : FetchEvent Page)
    (request : Request Page) (ht : request.arrival ≤ event.time)
    {t : Time} (h : t ∈ schedule.serviceCandidates request) :
    t ∈ (Schedule.mk schedule.initialCache (schedule.events ++ [event])).serviceCandidates
      request := by
  have hc : (Schedule.mk schedule.initialCache (schedule.events ++ [event])).cacheBefore
        request.arrival =
      schedule.cacheBefore request.arrival := by
    simp [Schedule.cacheBefore, List.foldl_append, not_lt.mpr ht]
  simp only [Schedule.serviceCandidates, hc, List.filter_append, List.map_append,
    List.toFinset_append] at h ⊢
  split_ifs at h ⊢ <;> simp only [Finset.mem_insert, Finset.mem_union] at h ⊢ <;> tauto

/-- The invariant of the dynamic family after a request prefix. `anchor` is
the last requested page (or an arbitrary initial page for the empty prefix).
All schedules start from the common initial cache `initial`.  The sum counts
actual fetch events, including the installation of the caches. -/
structure DynamicRun (initial pages : Finset Page) (k : ℕ) (requests : List (Request Page))
    where
  schedule : Fin k → Schedule Page
  initialCache : ∀ i, (schedule i).initialCache = initial
  hole : Fin k → Page
  anchor : Page
  anchor_mem : anchor ∈ pages
  hole_mem : ∀ i, hole i ∈ pages
  hole_injective : Function.Injective hole
  hole_ne : ∀ i, hole i ≠ anchor
  now : Time
  now_origin : now = 0 ∨ ∃ r ∈ requests, now = r.arrival
  request_time : ∀ r ∈ requests, r.arrival ≤ now
  event_time : ∀ i e, e ∈ (schedule i).events → e.time ≤ now
  chronological : ∀ i, (schedule i).events.Pairwise (fun a b => a.time ≤ b.time)
  transitions : ∀ i, Schedule.ValidTransitionsFrom initial (schedule i).events
  capacity : ∀ i e, e ∈ (schedule i).events → e.cacheAfter.card ≤ k
  cache : ∀ i, (schedule i).events.foldl (fun _ e => e.cacheAfter) initial = pages.erase (hole i)
  served : ∀ i r, r ∈ requests → r.arrival ∈ (schedule i).serviceCandidates r
  fetch_bound : (∑ i, (schedule i).fetchCount) ≤ k * k + requests.length

private theorem erased_card {pages : Finset Page} {k : ℕ}
    (hcard : pages.card = k + 1) {p : Page} (hp : p ∈ pages) :
    (pages.erase p).card = k := by
  rw [Finset.card_erase_of_mem hp, hcard]
  omega

/-- Initialize exactly `k` comparators, each with a different hole. -/
def DynamicRun.initial (initial pages : Finset Page) (k : ℕ) (hcard : pages.card = k + 1)
    (hinitial : initial.card ≤ k)
    (anchor : Page) (ha : anchor ∈ pages) : DynamicRun initial pages k [] := by
  let index : Fin k ≃ ↥(pages.erase anchor) := Fintype.equivOfCardEq (by
    simp [erased_card hcard ha])
  let hole : Fin k → Page := fun i => (index i).val
  have hm (i : Fin k) : hole i ∈ pages := (Finset.mem_erase.mp (index i).property).2
  have hn (i : Fin k) : hole i ≠ anchor := (Finset.mem_erase.mp (index i).property).1
  let schedule : Fin k → Schedule Page := fun i =>
    ⟨initial, Analysis.resetEvents initial (pages.erase (hole i))⟩
  exact
    { schedule := schedule
      initialCache := fun _ => rfl
      hole := hole
      anchor := anchor
      anchor_mem := ha
      hole_mem := hm
      hole_injective := fun i j h => index.injective (Subtype.ext h)
      hole_ne := hn
      now := 0
      now_origin := Or.inl rfl
      request_time := by simp
      event_time := fun i e he => (Analysis.resetEvents_time _ _ e he).le
      chronological := fun i => List.pairwise_of_forall_mem_list fun a ha b hb => by
        rw [Analysis.resetEvents_time _ _ a ha, Analysis.resetEvents_time _ _ b hb]
      transitions := fun i => Analysis.resetEvents_valid _ _
      capacity := fun i e he => by
        simpa [erased_card hcard (hm i)] using
          Finset.card_le_card (Analysis.resetEvents_cache_subset _ _ e he)
      cache := fun i => Analysis.resetEvents_fold _ _
        (hinitial.trans_eq (erased_card hcard (hm i)).symm)
      served := by simp
      fetch_bound := by
        refine (Finset.sum_le_card_nsmul _ _ k fun i _ => ?_).trans (by simp)
        simpa [schedule, Schedule.fetchCount, erased_card hcard (hm i)] using
          Analysis.resetEvents_length_le initial (pages.erase (hole i)) }

/-- A move fetches the requested hole and leaves the previous anchor absent. -/
def DynamicRun.advanceSchedule {initial pages : Finset Page} {k : ℕ}
    {requests : List (Request Page)} (run : DynamicRun initial pages k requests)
    (request : Request Page) (i : Fin k) : Schedule Page :=
  if run.hole i = request.page then
    ⟨(run.schedule i).initialCache,
      (run.schedule i).events ++ [⟨request.arrival, request.page, pages.erase run.anchor⟩]⟩
  else run.schedule i

def DynamicRun.advanceHole {initial pages : Finset Page} {k : ℕ}
    {requests : List (Request Page)} (run : DynamicRun initial pages k requests)
    (request : Request Page) (i : Fin k) : Page :=
  if run.hole i = request.page then run.anchor else run.hole i

/-- One request causes at most one movement in the whole family. -/
theorem DynamicRun.advance_fetch_bound {initial pages : Finset Page} {k : ℕ}
    {requests : List (Request Page)} (run : DynamicRun initial pages k requests)
    (request : Request Page) :
    (∑ i, (run.advanceSchedule request i).fetchCount) ≤
      (∑ i, (run.schedule i).fetchCount) + 1 := by
  have hc (i : Fin k) : (run.advanceSchedule request i).fetchCount =
      (run.schedule i).fetchCount + if run.hole i = request.page then 1 else 0 := by
    by_cases h : run.hole i = request.page <;>
      simp [advanceSchedule, h, Schedule.fetchCount]
  simp only [hc, Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]
  gcongr
  exact Finset.card_le_one.mpr fun i hi j hj => run.hole_injective (by simp_all)

/-- Extend the family by one strictly later request. All previously served
requests remain served at arrival, and the new request is served immediately. -/
def DynamicRun.advance {initial pages : Finset Page} {k : ℕ}
    (hcard : pages.card = k + 1) {requests : List (Request Page)}
    (run : DynamicRun initial pages k requests) (request : Request Page)
    (hp : request.page ∈ pages) (ht : run.now < request.arrival) :
    DynamicRun initial pages k (requests ++ [request]) := by
  -- the moving strategy appends one event, stamped `request.arrival`
  have hevents (i : Fin k) (e : FetchEvent Page)
      (he : e ∈ (run.advanceSchedule request i).events) :
      e ∈ (run.schedule i).events ∨
        e = ⟨request.arrival, request.page, pages.erase run.anchor⟩ := by
    unfold advanceSchedule at he
    split at he <;> simp_all
  refine
    { schedule := run.advanceSchedule request
      initialCache := fun i => by unfold advanceSchedule; split <;> exact run.initialCache i
      hole := run.advanceHole request
      anchor := request.page
      anchor_mem := hp
      hole_mem := fun i => by unfold advanceHole; split <;> simp [run.anchor_mem, run.hole_mem]
      hole_injective := ?_
      hole_ne := ?_
      now := request.arrival
      now_origin := Or.inr ⟨request, by simp, rfl⟩
      request_time := ?_
      event_time := ?_
      chronological := ?_
      transitions := ?_
      capacity := ?_
      cache := ?_
      served := ?_
      fetch_bound := ?_ }
  · intro i j hij
    dsimp [advanceHole] at hij
    split_ifs at hij with hi hj hj
    · exact run.hole_injective (hi.trans hj.symm)
    · exact (run.hole_ne j hij.symm).elim
    · exact (run.hole_ne i hij).elim
    · exact run.hole_injective hij
  · intro i
    unfold advanceHole
    split
    · exact fun he => run.hole_ne i (‹run.hole i = request.page›.trans he.symm)
    · assumption
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    exacts [(run.request_time r hr).trans ht.le, le_rfl]
  · intro i e he
    rcases hevents i e he with he | rfl
    exacts [(run.event_time i e he).trans ht.le, le_rfl]
  · intro i
    dsimp [advanceSchedule]
    split
    · refine List.pairwise_append.mpr ⟨run.chronological i, by simp, fun a ha b hb => ?_⟩
      rw [List.mem_singleton.mp hb]
      exact (run.event_time i a ha).trans ht.le
    · exact run.chronological i
  · intro i
    dsimp [advanceSchedule]
    split
    · rename_i hi
      apply Analysis.validTransitions_append _ _ _ (run.transitions i)
      rw [run.cache]
      have hne : request.page ≠ run.anchor := by simpa [hi] using run.hole_ne i
      refine ⟨Finset.mem_erase.mpr ⟨hne, hp⟩, ?_, trivial⟩
      rw [hi]
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
      aesop
    · exact run.transitions i
  · intro i e he
    rcases hevents i e he with he | rfl
    exacts [run.capacity i e he, (erased_card hcard run.anchor_mem).le]
  · intro i
    by_cases hi : run.hole i = request.page
    · simp [advanceSchedule, advanceHole, hi, List.foldl_append]
    · simpa [advanceSchedule, advanceHole, hi] using run.cache i
  · simp only [List.mem_append, List.mem_singleton]
    rintro i r (hr | hr) <;> by_cases hi : run.hole i = request.page
    · simp only [advanceSchedule, if_pos hi]
      exact candidate_append _ _ r ((run.request_time r hr).trans ht.le) (run.served i r hr)
    · simpa [advanceSchedule, hi] using run.served i r hr
    · subst r
      simp only [advanceSchedule, if_pos hi]
      exact LowerBound.mem_serviceCandidates_of_fetch _ _
        (event := ⟨request.arrival, request.page, pages.erase run.anchor⟩) (by simp) le_rfl rfl
    · subst r
      simp only [advanceSchedule, if_neg hi]
      apply LowerBound.arrival_mem_serviceCandidates_of_hit
      rw [Schedule.cacheBefore, foldl_cacheBefore_eq _ _ fun e he =>
        (run.event_time i e he).trans_lt ht, run.initialCache, run.cache]
      exact Finset.mem_erase.mpr ⟨Ne.symm hi, hp⟩
  · have h := run.advance_fetch_bound request
    have hb := run.fetch_bound
    simp only [List.length_append, List.length_singleton]
    omega

/-- Build the dynamic family for any strictly chronological request sequence
whose arrivals are positive and whose pages lie in the chosen universe. -/
theorem exists_dynamicRun (initial pages : Finset Page) (k : ℕ)
    (hcard : pages.card = k + 1) (hinitial : initial.card ≤ k) (requests : List (Request Page))
    (hstrict : requests.Pairwise (fun a b => a.arrival < b.arrival))
    (hrequests : ∀ r ∈ requests, r.page ∈ pages ∧ 0 < r.arrival) :
    Nonempty (DynamicRun initial pages k requests) := by
  induction requests using List.reverseRecOn with
  | nil =>
      have hne : pages.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨anchor, ha⟩ := hne
      exact ⟨DynamicRun.initial initial pages k hcard hinitial anchor ha⟩
  | append_singleton requests request ih =>
      have hs := List.pairwise_append.mp hstrict
      obtain ⟨run⟩ := ih hs.1 (fun r hr => hrequests r (List.mem_append_left _ hr))
      have hr := hrequests request (by simp)
      have ht : run.now < request.arrival := by
        rcases run.now_origin with hz | ⟨r, hm, he⟩
        · simpa [hz] using hr.2
        · rw [he]
          exact hs.2.2 r hm request (by simp)
      exact ⟨run.advance hcard request hr.1 ht⟩

/-- The dynamic comparators in the trusted schedule model: every request is
served at arrival, so the aggregate cost is at most `k² + number of requests`.
The `k²` term pays to install all `k` caches. -/
theorem exists_dynamic_comparators (input : Instance Page)
    (pages : Finset Page) (hcard : pages.card = input.cacheSize + 1)
    (hstrict : input.requests.Pairwise (fun a b => a.arrival < b.arrival))
    (hrequests : ∀ r ∈ input.requests, r.page ∈ pages ∧ 0 < r.arrival) :
    ∃ comparator : Fin input.cacheSize → Schedule Page,
      (∀ i, (comparator i).Feasible input) ∧
      (∑ i, (comparator i).totalCost input) ≤
        (input.cacheSize : Cost) * input.cacheSize + input.requests.length := by
  obtain ⟨run⟩ := exists_dynamicRun input.initialCache.toFinset pages input.cacheSize hcard
    (initialCache_card_le input) input.requests hstrict hrequests
  have hzero (i : Fin input.cacheSize) : (run.schedule i).totalDelay input = 0 :=
    List.sum_eq_zero fun c hc => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
      exact LowerBound.requestCost_eq_zero_of_arrival_mem _ _ (run.served i r hr)
  refine ⟨run.schedule, fun i => ⟨run.initialCache i, run.chronological i,
    (run.initialCache i).symm ▸ run.transitions i, run.capacity i,
    fun r hr => ⟨r.arrival, run.served i r hr⟩⟩, ?_⟩
  simp only [Schedule.totalCost, hzero, add_zero]
  exact_mod_cast run.fetch_bound

end
end PagingWithDelay.GeneralLowerBound
