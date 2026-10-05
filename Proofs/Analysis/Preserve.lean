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
  induction l with
  | nil => simp
  | cons b rest ih =>
      have hrest := ih (fun a ha => himp a (List.mem_cons_of_mem _ ha))
      by_cases hb : p b = true
      · have hqb := himp b (by simp) hb
        simp only [List.filter_cons, hb, hqb, if_pos, List.length_cons]
        omega
      · simp only [Bool.not_eq_true] at hb
        rw [List.filter_cons_of_neg (by simp [hb])]
        by_cases hqb : q b = true
        · rw [List.filter_cons_of_pos hqb]
          simp only [List.length_cons]
          omega
        · simp only [Bool.not_eq_true] at hqb
          rw [List.filter_cons_of_neg (by simp [hqb])]
          exact hrest

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
      rcases List.mem_cons.mp ha with rfl | ha'
      · rw [List.filter_cons_of_neg (by simp [hp]), List.filter_cons_of_pos hq]
        have := length_filter_le_of_imp rest p q himp'
        simp only [List.length_cons]
        omega
      · have hrest := ih himp' ha'
        by_cases hb : p b = true
        · have hqb := himp b (by simp) hb
          rw [List.filter_cons_of_pos hb, List.filter_cons_of_pos hqb]
          simpa using hrest
        · simp only [Bool.not_eq_true] at hb
          rw [List.filter_cons_of_neg (by simp [hb])]
          by_cases hqb : q b = true
          · rw [List.filter_cons_of_pos hqb]
            simp only [List.length_cons]
            omega
          · simp only [Bool.not_eq_true] at hqb
            rw [List.filter_cons_of_neg (by simp [hqb])]
            exact hrest

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
    constructor
    · rintro ⟨e, ⟨he, hdec⟩, rfl⟩
      exact ⟨e, ⟨(hevents e htime).mp he, hdec⟩, rfl⟩
    · rintro ⟨e, ⟨he, hdec⟩, rfl⟩
      exact ⟨e, ⟨(hevents e htime).mpr he, hdec⟩, rfl⟩
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
    (online : Online algorithm) (input : Instance Page) (valid : input.Valid)
    (request : Request Page) (extendedValid : (input.appendRequest request).Valid)
    (e : FetchEvent Page) (he : e.time < request.arrival) :
    e ∈ (algorithm (input.appendRequest request) extendedValid).events ↔
      e ∈ (algorithm input valid).events := by
  have hprefix := online.appendRequest_prefix input valid request extendedValid he
  constructor
  · intro hmem
    have : e ∈ ((algorithm (input.appendRequest request) extendedValid).upTo e.time).events :=
      List.mem_filter.mpr ⟨hmem, by simp⟩
    rw [hprefix] at this
    exact (List.mem_filter.mp this).1
  · intro hmem
    have : e ∈ ((algorithm input valid).upTo e.time).events :=
      List.mem_filter.mpr ⟨hmem, by simp⟩
    rw [← hprefix] at this
    exact (List.mem_filter.mp this).1

/-- A request already served before the new arrival keeps its service time. -/
theorem Online.appendRequest_serviceTime {algorithm : Algorithm Page}
    (online : Online algorithm) (feasible : Feasible algorithm)
    (input : Instance Page) (valid : input.Valid)
    (request : Request Page) (extendedValid : (input.appendRequest request).Valid)
    (earlier : Request Page) (harrival : earlier.arrival < request.arrival)
    {time : Time} (htime : time < request.arrival)
    (hservice : (algorithm input valid).serviceTime earlier = some time) :
    (algorithm (input.appendRequest request) extendedValid).serviceTime earlier = some time := by
  set old := algorithm input valid with hold
  set new := algorithm (input.appendRequest request) extendedValid with hnew
  have hcache : new.cacheBefore earlier.arrival = old.cacheBefore earlier.arrival := by
    apply online.cacheBefore_eq feasible _ _ _ _ (by rfl)
    intro s hs
    exact input.appendRequest_upTo request (hs.trans harrival)
  have hevents : ∀ e : FetchEvent Page, e.time < request.arrival →
      (e ∈ new.events ↔ e ∈ old.events) :=
    fun e he => online.appendRequest_mem_events input valid request extendedValid e he
  have hcongr : ∀ {t : Time}, t < request.arrival →
      (t ∈ new.serviceCandidates earlier ↔ t ∈ old.serviceCandidates earlier) :=
    fun {t} ht => Schedule.mem_serviceCandidates_congr earlier hcache hevents ht
  obtain ⟨hmem, hle⟩ := (Schedule.serviceTime_eq_some_iff _ _ _).mp hservice
  refine (Schedule.serviceTime_eq_some_iff _ _ _).mpr ⟨(hcongr htime).mpr hmem, ?_⟩
  intro candidate hcandidate
  by_cases hlt : candidate < request.arrival
  · exact hle candidate ((hcongr hlt).mp hcandidate)
  · exact htime.le.trans (not_lt.mp hlt)

/-- Consequently the delay cost of every earlier served request is unchanged. -/
theorem Online.appendRequest_requestCost {algorithm : Algorithm Page}
    (online : Online algorithm) (feasible : Feasible algorithm)
    (input : Instance Page) (valid : input.Valid)
    (request : Request Page) (extendedValid : (input.appendRequest request).Valid)
    (earlier : Request Page) (harrival : earlier.arrival < request.arrival)
    {time : Time} (htime : time < request.arrival)
    (hservice : (algorithm input valid).serviceTime earlier = some time) :
    (algorithm (input.appendRequest request) extendedValid).requestCost earlier =
      (algorithm input valid).requestCost earlier := by
  rw [Schedule.requestCost_of_serviceTime _ _ _
      (online.appendRequest_serviceTime feasible input valid request extendedValid earlier
        harrival htime hservice),
    Schedule.requestCost_of_serviceTime _ _ _ hservice]

end
end Algorithm

end PagingWithDelay
