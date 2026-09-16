import PagingWithDelay.Online

/-!
# Extending inputs against an arbitrary online algorithm

The definition of onlineness uses closed prefixes. Adaptive constructions
also need the cache immediately before a new arrival: it is determined by
the strictly earlier requests, even when the algorithm reacts at the arrival
time itself. These lemmas use only the trusted model, not the FIFO event loop.
-/

namespace PagingWithDelay

variable {Page : Type*} [DecidableEq Page]

noncomputable section

namespace Schedule

/-- Capacity also bounds the cache between fetch events, the initial cache
included. -/
theorem cacheBefore_card_le (schedule : Schedule Page) (input : Instance Page)
    (hvalid : input.Valid) (feasible : schedule.Feasible input) (t : Time) :
    (schedule.cacheBefore t).card ≤ input.cacheSize := by
  have hfold (events : List (FetchEvent Page)) (initial : Finset Page)
      (hi : initial.card ≤ input.cacheSize)
      (he : ∀ e ∈ events, e.cacheAfter.card ≤ input.cacheSize) :
      (events.foldl (fun cache e => if e.time < t then e.cacheAfter else cache)
        initial).card ≤ input.cacheSize := by
    induction events generalizing initial with
    | nil => exact hi
    | cons e rest ih =>
        apply ih
        · dsimp only
          split
          · exact he e (by simp)
          · exact hi
        · intro e he'
          exact he e (List.mem_cons_of_mem _ he')
  refine hfold schedule.events schedule.initialCache ?_ feasible.capacity
  rw [feasible.initialCache]
  exact (List.toFinset_card_le _).trans hvalid.initialCache_full.le

private theorem exists_cutoff (events : List (FetchEvent Page))
    {t : Time} (ht : 0 < t) :
    ∃ s : Time, s < t ∧ ∀ event ∈ events, event.time < t → event.time ≤ s := by
  induction events with
  | nil => exact ⟨0, ht, by simp⟩
  | cons event rest ih =>
      obtain ⟨s, hs, hrest⟩ := ih
      by_cases he : event.time < t
      · refine ⟨max s event.time, max_lt hs he, ?_⟩
        intro other hother htime
        rcases List.mem_cons.mp hother with rfl | hother
        · exact le_max_right _ _
        · exact (hrest other hother htime).trans (le_max_left _ _)
      · refine ⟨s, hs, ?_⟩
        intro other hother htime
        rcases List.mem_cons.mp hother with rfl | hother
        · exact (he htime).elim
        · exact hrest other hother htime

/-- Equal closed traces at every earlier cutoff imply equal open traces.
Finiteness of the schedules lets us choose a single earlier cutoff containing
all events strictly before `t`. -/
theorem events_before_eq_of_prefix_eq (first second : Schedule Page) (t : Time)
    (h : ∀ s < t, first.upTo s = second.upTo s) :
    first.events.filter (fun e => decide (e.time < t)) =
      second.events.filter (fun e => decide (e.time < t)) := by
  by_cases ht : t = 0
  · simp [ht]
  obtain ⟨s, hst, hbound⟩ := exists_cutoff (first.events ++ second.events)
    (pos_iff_ne_zero.mpr ht)
  have hfilter (events : List (FetchEvent Page))
      (hmem : ∀ e ∈ events, e ∈ first.events ++ second.events) :
      events.filter (fun e => decide (e.time < t)) =
        events.filter (fun e => decide (e.time ≤ s)) := by
    apply List.filter_congr
    intro e he
    simp only [decide_eq_decide]
    exact ⟨hbound e (hmem e he), fun hle => hle.trans_lt hst⟩
  rw [hfilter first.events (fun _ he => List.mem_append_left _ he),
    hfilter second.events (fun _ he => List.mem_append_right _ he)]
  exact congrArg Schedule.events (h s hst)

/-- In particular, a cache before `t` depends only on the earlier trace and
the initial cache.  The initial cache is a separate hypothesis: at `t = 0`
there is no earlier cutoff to read it from. -/
theorem cacheBefore_eq_of_prefix_eq (first second : Schedule Page) (t : Time)
    (hinitial : first.initialCache = second.initialCache)
    (h : ∀ s < t, first.upTo s = second.upTo s) :
    first.cacheBefore t = second.cacheBefore t := by
  have hfold (schedule : Schedule Page) : schedule.cacheBefore t =
      (schedule.events.filter (fun e => decide (e.time < t))).foldl
        (fun _ e => e.cacheAfter) schedule.initialCache := by
    simp [cacheBefore, List.foldl_filter]
  rw [hfold first, hfold second, events_before_eq_of_prefix_eq first second t h, hinitial]

end Schedule

namespace Algorithm

/-- Requests arriving at `t` cannot affect the cache *before* `t`, although
they can affect the fetch events stamped exactly `t`.  Feasibility pins the
initial caches to those of the instances, which must agree. -/
theorem Online.cacheBefore_eq {algorithm : Algorithm Page} (online : Online algorithm)
    (feasible : Feasible algorithm)
    (first second : Instance Page) (hfirst : first.Valid) (hsecond : second.Valid)
    (hinitial : first.initialCache = second.initialCache)
    (t : Time) (h : ∀ s < t, first.upTo s = second.upTo s) :
    (algorithm first hfirst).cacheBefore t = (algorithm second hsecond).cacheBefore t := by
  apply Schedule.cacheBefore_eq_of_prefix_eq
  · rw [(feasible.scheduleFeasible first hfirst).initialCache,
      (feasible.scheduleFeasible second hsecond).initialCache, hinitial]
  intro s hs
  exact online.prefixDetermined first second hfirst hsecond s (h s hs)

end Algorithm

namespace Instance

/-- Append one newly revealed request to an adaptive prefix. -/
def appendRequest (input : Instance Page) (request : Request Page) : Instance Page :=
  { input with requests := input.requests ++ [request] }

omit [DecidableEq Page] in
theorem Valid.appendRequest {input : Instance Page} (valid : input.Valid)
    (request : Request Page) (hlast : ∀ r ∈ input.requests, r.arrival ≤ request.arrival) :
    (input.appendRequest request).Valid where
  positiveCapacity := valid.positiveCapacity
  initialCache_nodup := valid.initialCache_nodup
  initialCache_full := valid.initialCache_full
  chronological := by
    simpa [Chronological, Instance.appendRequest, List.pairwise_append] using
      And.intro valid.chronological hlast

omit [DecidableEq Page] in
theorem appendRequest_upTo (input : Instance Page) (request : Request Page)
    {t : Time} (ht : t < request.arrival) :
    (input.appendRequest request).upTo t = input.upTo t := by
  simp [Instance.upTo, Instance.appendRequest, not_le.mpr ht]

end Instance

namespace Algorithm

/-- Appending a request preserves all actions strictly before its arrival. -/
theorem Online.appendRequest_prefix {algorithm : Algorithm Page} (online : Online algorithm)
    (input : Instance Page) (valid : input.Valid) (request : Request Page)
    (extendedValid : (input.appendRequest request).Valid)
    {t : Time} (ht : t < request.arrival) :
    (algorithm (input.appendRequest request) extendedValid).upTo t =
      (algorithm input valid).upTo t :=
  online.prefixDetermined _ _ extendedValid valid t (input.appendRequest_upTo request ht)

/-- The next requested page can be chosen from the old run's cache complement:
the new run has exactly the same cache immediately before that request. -/
theorem Online.appendRequest_cacheBefore {algorithm : Algorithm Page}
    (online : Online algorithm) (feasible : Feasible algorithm)
    (input : Instance Page) (valid : input.Valid)
    (request : Request Page) (extendedValid : (input.appendRequest request).Valid) :
    (algorithm (input.appendRequest request) extendedValid).cacheBefore request.arrival =
      (algorithm input valid).cacheBefore request.arrival := by
  apply online.cacheBefore_eq feasible _ _ _ _ (by rfl)
  intro s hs
  exact input.appendRequest_upTo request hs

end Algorithm

end
end PagingWithDelay
