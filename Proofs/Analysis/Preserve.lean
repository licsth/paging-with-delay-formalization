import Proofs.Analysis.Adaptive

/-!
# What an appended request leaves untouched

`Analysis/Adaptive.lean` shows that appending a request preserves the events
strictly before its arrival and the cache immediately before it. The adaptive
lower-bound construction also needs that the *service* of the earlier requests
is unchanged: a request already served before the new arrival keeps its service
time, hence its delay cost, in the extended run.

Everything here is stated for arbitrary schedules and uses only the trusted
model.
-/

namespace PagingWithDelay

variable {Page : Type*} [DecidableEq Page]

/-! ### Two list lemmas about filtering by a widening predicate -/

namespace Analysis

theorem length_filter_le_of_imp {α : Type*} (l : List α) (p q : α → Bool)
    (himp : ∀ a ∈ l, p a = true → q a = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  simpa [← List.countP_eq_length_filter] using List.countP_mono_left himp

/-- A widening predicate that newly admits some member of the list filters
strictly more of it. -/
theorem length_filter_lt_of_imp {α : Type*} (l : List α) (p q : α → Bool)
    (himp : ∀ a ∈ l, p a = true → q a = true) {a : α} (ha : a ∈ l)
    (hp : p a = false) (hq : q a = true) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => simp at ha
  | cons b rest ih =>
      have himp' : ∀ x ∈ rest, p x = true → q x = true :=
        fun x hx => himp x (List.mem_cons_of_mem _ hx)
      have hle := length_filter_le_of_imp rest p q himp'
      have hb := himp b (by simp)
      rcases List.mem_cons.mp ha with rfl | ha'
      · simp [hp, hq]
        omega
      · have := ih himp' ha'
        simp only [List.filter_cons]
        split_ifs <;> simp_all

end Analysis

namespace Schedule

noncomputable section

/-- Being the derived service time is exactly being a least candidate. -/
theorem serviceTime_eq_some_iff (schedule : Schedule Page) (request : Request Page)
    (time : Time) :
    schedule.serviceTime request = some time ↔
      time ∈ schedule.serviceCandidates request ∧
        ∀ candidate ∈ schedule.serviceCandidates request, time ≤ candidate := by
  constructor
  · intro h
    unfold serviceTime at h
    split at h
    · rename_i hne
      obtain rfl : time = (schedule.serviceCandidates request).min' hne :=
        (Option.some_inj.mp h).symm
      exact ⟨Finset.min'_mem _ _, fun c hc => Finset.min'_le _ _ hc⟩
    · cases h
  · rintro ⟨hmem, hle⟩
    have hne : (schedule.serviceCandidates request).Nonempty := ⟨time, hmem⟩
    rw [serviceTime, dif_pos hne]
    exact congrArg some
      (le_antisymm (Finset.min'_le _ _ hmem) (hle _ (Finset.min'_mem _ _)))

/-- The delay cost of a request with a known service time. -/
theorem requestCost_of_serviceTime (schedule : Schedule Page) (request : Request Page)
    (time : Time) (hservice : schedule.serviceTime request = some time) :
    schedule.requestCost request = request.delay (time - request.arrival) := by
  unfold requestCost serviceDelay
  rw [hservice]
  rfl

/-- Two schedules agreeing on the cache before a request and on all events
before a cutoff have the same service candidates before that cutoff. -/
theorem mem_serviceCandidates_congr {first second : Schedule Page}
    (request : Request Page) {cut : Time}
    (hcache : first.cacheBefore request.arrival = second.cacheBefore request.arrival)
    (hevents : ∀ e : FetchEvent Page, e.time < cut → (e ∈ first.events ↔ e ∈ second.events))
    {time : Time} (htime : time < cut) :
    time ∈ first.serviceCandidates request ↔ time ∈ second.serviceCandidates request := by
  have hfetch : time ∈ ((first.events.filter fun e =>
        decide (request.arrival ≤ e.time ∧ request.page = e.fetched)).map
        FetchEvent.time).toFinset ↔
      time ∈ ((second.events.filter fun e =>
        decide (request.arrival ≤ e.time ∧ request.page = e.fetched)).map
        FetchEvent.time).toFinset := by
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter]
    exact exists_congr fun e => and_congr_left fun hte =>
      and_congr_left fun _ => hevents e (hte ▸ htime)
  unfold serviceCandidates
  simp only [hcache]
  split
  · simp only [Finset.mem_insert]
    exact or_congr_right hfetch
  · exact hfetch

end
end Schedule

namespace Algorithm

noncomputable section

/-- Appending a request does not change which events happen before its
arrival. -/
theorem Online.appendRequest_mem_events {algorithm : Algorithm Page}
    (online : Online algorithm) (input : Instance Page)
    (request : Request Page) (hlast : ∀ r ∈ input.requests, r.arrival ≤ request.arrival)
    (e : FetchEvent Page) (he : e.time < request.arrival) :
    e ∈ (algorithm (input.appendRequest request hlast)).events ↔
      e ∈ (algorithm input).events := by
  simpa [Schedule.upTo] using
    congrArg (e ∈ ·.events) (online.appendRequest_prefix input request hlast he)

/-- A request already served before the new arrival keeps its service time. -/
theorem Online.appendRequest_serviceTime {algorithm : Algorithm Page}
    (online : Online algorithm) (input : Instance Page) (request : Request Page)
    (hlast : ∀ r ∈ input.requests, r.arrival ≤ request.arrival)
    (earlier : Request Page) (harrival : earlier.arrival < request.arrival)
    {time : Time} (htime : time < request.arrival)
    (hservice : (algorithm input).serviceTime earlier = some time) :
    (algorithm (input.appendRequest request hlast)).serviceTime earlier = some time := by
  have hcache : (algorithm (input.appendRequest request hlast)).cacheBefore earlier.arrival =
      (algorithm input).cacheBefore earlier.arrival :=
    online.cacheBefore_eq _ _ (by rfl) _ fun _ hs =>
      input.appendRequest_upTo request hlast (hs.trans harrival)
  have hcongr {t : Time} (ht : t < request.arrival) :=
    Schedule.mem_serviceCandidates_congr earlier hcache
      (online.appendRequest_mem_events input request hlast) ht
  obtain ⟨hmem, hle⟩ := (Schedule.serviceTime_eq_some_iff _ _ _).mp hservice
  refine (Schedule.serviceTime_eq_some_iff _ _ _).mpr ⟨(hcongr htime).mpr hmem, ?_⟩
  intro candidate hcandidate
  by_cases hlt : candidate < request.arrival
  · exact hle candidate ((hcongr hlt).mp hcandidate)
  · exact htime.le.trans (not_lt.mp hlt)

/-- Consequently the delay cost of every earlier served request is unchanged. -/
theorem Online.appendRequest_requestCost {algorithm : Algorithm Page}
    (online : Online algorithm) (input : Instance Page) (request : Request Page)
    (hlast : ∀ r ∈ input.requests, r.arrival ≤ request.arrival)
    (earlier : Request Page) (harrival : earlier.arrival < request.arrival)
    {time : Time} (htime : time < request.arrival)
    (hservice : (algorithm input).serviceTime earlier = some time) :
    (algorithm (input.appendRequest request hlast)).requestCost earlier =
      (algorithm input).requestCost earlier := by
  rw [Schedule.requestCost_of_serviceTime _ _ _
      (online.appendRequest_serviceTime input request hlast earlier
        harrival htime hservice),
    Schedule.requestCost_of_serviceTime _ _ _ hservice]

end
end Algorithm

end PagingWithDelay
