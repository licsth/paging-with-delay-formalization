import PagingWithDelay.Analysis.Preserve
import PagingWithDelay.Analysis.GeometricDelay

/-!
# The adaptive request sequence of the general lower bound

The construction of the write-up, phase by phase. A phase begins by requesting
a page the online algorithm does not hold, immediately after the previous
phase ended, and ends when the algorithm serves that request.

`AdversaryRun` is the invariant carried along the phases:

* every request so far has been served by the current time `now`, and each
  phase has forced one more fetch before `now`;
* the requests have geometrically increasing linear delay rates, so all
  earlier rates together are at most `ε` times the next rate `nextSlope`;
* holding *every* request until `now`, which is what the static offline
  strategies of `Static.lean` do, costs at most `(1+ε)` times the algorithm's
  own delay, plus a spent budget `used` which never exceeds `1`.

The gap between the end of a phase and the next arrival must be positive --
`Model.lean` serves arrivals before transitions with the same timestamp -- and
is chosen small enough for the current phase to spend at most half of the
remaining budget.
-/

namespace PagingWithDelay.GeneralLowerBound

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-! ### Two facts about truncated subtraction of times -/

private theorem add_tsub_comm {a b : Time} (h : a ≤ b) (d : Time) :
    b + d - a = b - a + d := by
  rw [tsub_add_eq_add_tsub h]

private theorem tsub_split {a b : Time} (gap : Time) (h : a + gap ≤ b) :
    b - a = b - (a + gap) + gap := by
  have hgap : gap ≤ b - a := le_tsub_of_add_le_left h
  rw [tsub_add_eq_tsub_tsub, tsub_add_cancel_of_le hgap]

/-- The invariant maintained after finitely many phases of the construction. -/
structure AdversaryRun (algorithm : Algorithm Page) (k : ℕ) (pages : Finset Page)
    (c ε : Cost) where
  /-- The requests revealed so far. -/
  input : Instance Page
  valid : input.Valid
  size : input.cacheSize = k
  memPages : ∀ r ∈ input.requests, r.page ∈ pages
  positive : ∀ r ∈ input.requests, 0 < r.arrival
  strict : input.requests.Pairwise fun earlier later => earlier.arrival < later.arrival
  /-- The end of the last phase. -/
  now : Time
  arrivalLe : ∀ r ∈ input.requests, r.arrival ≤ now
  served : ∀ r ∈ input.requests, ∃ s ≤ now, (algorithm input valid).serviceTime r = some s
  /-- Each phase forced one fetch, all of them before `now`. -/
  fetches : input.requests.length ≤ ((algorithm input valid).upTo now).events.length
  /-- The delay rate of all revealed requests together, and the rate of the
  request the next phase will issue. -/
  slopeTotal : Cost
  nextSlope : Cost
  nextSlopePos : 0 < nextSlope
  shift : ∀ d : Time,
    (input.requests.map fun r => r.delay (now + d - r.arrival)).sum =
      (input.requests.map fun r => r.delay (now - r.arrival)).sum + slopeTotal * d
  slopeTotalLe : slopeTotal ≤ ε * nextSlope
  /-- The perturbation budget, spent on the gaps between phases. -/
  used : Cost
  budget : Cost
  budgetPos : 0 < budget
  budgetTotal : used + budget ≤ 1
  delayBound : (input.requests.map fun r => r.delay (now - r.arrival)).sum ≤
      (1 + ε) * (algorithm input valid).totalDelay input + used

/-- Before the first request, the invariant is trivial. -/
def AdversaryRun.initial (algorithm : Algorithm Page) {k : ℕ} (hk : 0 < k)
    (pages : Finset Page) (c ε : Cost) : AdversaryRun algorithm k pages c ε where
  input := ⟨k, []⟩
  valid := ⟨List.Pairwise.nil, hk⟩
  size := rfl
  memPages := by simp
  positive := by simp
  strict := List.Pairwise.nil
  now := 0
  arrivalLe := by simp
  served := by simp
  fetches := by simp
  slopeTotal := 0
  nextSlope := 1
  nextSlopePos := zero_lt_one
  shift := by simp
  slopeTotalLe := by simp
  used := 0
  budget := 1
  budgetPos := zero_lt_one
  budgetTotal := by simp
  delayBound := by simp

/-- One further phase. The new request is placed on a page the algorithm does
not hold just before the new arrival, so it is a miss and forces a fetch; the
phase ends when that request is served. -/
theorem AdversaryRun.exists_advance {algorithm : Algorithm Page} (online : algorithm.Online)
    (feasible : ∀ input valid, (algorithm input valid).Feasible input)
    {k : ℕ} {pages : Finset Page} (hcard : pages.card = k + 1)
    {c ε : Cost} (hc : ε + 1 ≤ ε * c) (run : AdversaryRun algorithm k pages c ε) :
    ∃ next : AdversaryRun algorithm k pages c ε,
      next.input.requests.length = run.input.requests.length + 1 := by
  classical
  set old := algorithm run.input run.valid with hold
  -- the gap to the next arrival, small enough to spend half of the budget
  set rate : Cost := ε * run.nextSlope with hrate
  set gap : Time := run.budget / 2 / (rate + 1) with hgapdef
  have hratepos : (0 : Cost) < rate + 1 := by positivity
  have hgappos : 0 < gap := by
    rw [hgapdef]
    exact div_pos (half_pos run.budgetPos) hratepos
  have hgapbound : rate * gap ≤ run.budget / 2 := by
    rw [hgapdef, ← mul_div_assoc, div_le_iff₀ hratepos, mul_comm]
    gcongr
    exact le_self_add
  set arrival : Time := run.now + gap with harrivaldef
  have hnowlt : run.now < arrival := lt_add_of_pos_right _ hgappos
  have hcpos : (0 : Cost) < c := by
    rcases (zero_le c).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hc
      simp at hc
  -- a page the algorithm does not hold just before the new arrival
  have hcap := old.cacheBefore_card_le run.input (feasible _ _) arrival
  have hnsub : ¬pages ⊆ old.cacheBefore arrival := by
    intro h
    have hle := (Finset.card_le_card h).trans hcap
    rw [hcard, run.size] at hle
    omega
  obtain ⟨page, hpage, hmiss⟩ := Finset.not_subset.mp hnsub
  set request := Analysis.linearRequest page arrival run.nextSlope run.nextSlopePos with hreqdef
  have hreqarrival : request.arrival = arrival := rfl
  have hreqpage : request.page = page := rfl
  have hreqdelay : ∀ x : Time, request.delay x = run.nextSlope * x := fun _ => rfl
  have extendedValid : (run.input.appendRequest request).Valid :=
    run.valid.appendRequest request fun r hr => (run.arrivalLe r hr).trans hnowlt.le
  set new := algorithm (run.input.appendRequest request) extendedValid with hnew
  have hearlier : ∀ r ∈ run.input.requests, r.arrival < request.arrival :=
    fun r hr => lt_of_le_of_lt (run.arrivalLe r hr) hnowlt
  -- the miss persists in the extended run
  have hmiss' : request.page ∉ new.cacheBefore request.arrival := by
    rw [hnew, online.appendRequest_cacheBefore run.input run.valid request extendedValid]
    exact hmiss
  -- the end of the new phase
  have hmem : request ∈ (run.input.appendRequest request).requests := by
    simp [Instance.appendRequest]
  have hne := (feasible _ extendedValid).eventuallyServed request hmem
  set s : Time := (new.serviceCandidates request).min' hne with hsdef
  have hsmem : s ∈ new.serviceCandidates request := Finset.min'_mem _ _
  have hservice : new.serviceTime request = some s :=
    (Schedule.serviceTime_eq_some_iff _ _ _).mpr
      ⟨hsmem, fun t ht => Finset.min'_le _ _ ht⟩
  obtain ⟨event, hevent, heventtime, hearrival⟩ :
      ∃ e ∈ new.events, e.time = s ∧ request.arrival ≤ e.time := by
    simp only [Schedule.serviceCandidates, if_neg hmiss', List.mem_toFinset,
      List.mem_map] at hsmem
    obtain ⟨e, he, hetime⟩ := hsmem
    have hf := List.mem_filter.mp he
    exact ⟨e, hf.1, hetime, (of_decide_eq_true hf.2).1⟩
  have harrle : arrival ≤ s := heventtime ▸ hearrival
  have hnowle : run.now ≤ s := hnowlt.le.trans harrle
  set u : Time := s - arrival with hudef
  set w : Time := s - run.now with hwdef
  have hwu : w = u + gap := by
    rw [hwdef, hudef, harrivaldef]
    exact tsub_split gap (harrivaldef ▸ harrle)
  have hnoww : run.now + w = s := add_tsub_cancel_of_le hnowle
  -- service of the earlier requests is unchanged
  have hservedOld : ∀ r ∈ run.input.requests, ∃ t ≤ run.now, new.serviceTime r = some t := by
    intro r hr
    obtain ⟨t, htle, ht⟩ := run.served r hr
    exact ⟨t, htle, online.appendRequest_serviceTime run.input run.valid request extendedValid
      r (hearlier r hr) (lt_of_le_of_lt htle hnowlt) ht⟩
  have hcostOld : ∀ r ∈ run.input.requests, new.requestCost r = old.requestCost r := by
    intro r hr
    obtain ⟨t, htle, ht⟩ := run.served r hr
    exact online.appendRequest_requestCost run.input run.valid request extendedValid r
      (hearlier r hr) (lt_of_le_of_lt htle hnowlt) ht
  -- the algorithm's delay grows by exactly the delay of the new request
  have htotalDelay : new.totalDelay (run.input.appendRequest request) =
      old.totalDelay run.input + run.nextSlope * u := by
    simp only [Schedule.totalDelay, Instance.appendRequest, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    congr 1
    · exact congrArg List.sum (List.map_congr_left hcostOld)
    · rw [Schedule.requestCost_of_serviceTime _ _ _ hservice, hreqdelay, hreqarrival]
  -- the delay sums of the earlier requests, measured at the new time
  have hsumOld : ∀ d : Time,
      (run.input.requests.map fun r => r.delay (s + d - r.arrival)).sum =
        (run.input.requests.map fun r => r.delay (run.now - r.arrival)).sum +
          run.slopeTotal * (w + d) := by
    intro d
    rw [← hnoww, add_assoc]
    exact run.shift (w + d)
  have hsumNow : (run.input.requests.map fun r => r.delay (s - r.arrival)).sum =
      (run.input.requests.map fun r => r.delay (run.now - r.arrival)).sum +
        run.slopeTotal * w := by
    have := hsumOld 0
    simpa using this
  refine ⟨{
    input := run.input.appendRequest request
    valid := extendedValid
    size := run.size
    memPages := ?_
    positive := ?_
    strict := ?_
    now := s
    arrivalLe := ?_
    served := ?_
    fetches := ?_
    slopeTotal := run.slopeTotal + run.nextSlope
    nextSlope := c * run.nextSlope
    nextSlopePos := ?_
    shift := ?_
    slopeTotalLe := ?_
    used := run.used + rate * gap
    budget := run.budget / 2
    budgetPos := half_pos run.budgetPos
    budgetTotal := ?_
    delayBound := ?_ }, by simp [Instance.appendRequest]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact run.memPages r hr
    · rw [List.mem_singleton.mp hr, hreqpage]; exact hpage
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact run.positive r hr
    · rw [List.mem_singleton.mp hr, hreqarrival, harrivaldef]
      exact lt_of_lt_of_le hgappos le_add_self
  · refine List.pairwise_append.mpr ⟨run.strict, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton.mp hb]
    exact hearlier a ha
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (run.arrivalLe r hr).trans hnowle
    · rw [List.mem_singleton.mp hr, hreqarrival]; exact harrle
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨t, htle, ht⟩ := hservedOld r hr
      exact ⟨t, htle.trans hnowle, ht⟩
    · rw [List.mem_singleton.mp hr]
      exact ⟨s, le_rfl, hservice⟩
  · have hprefix : (new.upTo run.now).events = (old.upTo run.now).events := by
      rw [hnew, hold, online.appendRequest_prefix run.input run.valid request extendedValid
        (hreqarrival ▸ hnowlt)]
    have hstep : (new.upTo run.now).events.length < (new.upTo s).events.length := by
      apply Analysis.length_filter_lt_of_imp new.events _ _ _ hevent
      · exact decide_eq_false (by rw [heventtime]; exact not_le.mpr (lt_of_lt_of_le hnowlt harrle))
      · exact decide_eq_true (by rw [heventtime])
      · intro e _ he
        exact decide_eq_true ((of_decide_eq_true he).trans hnowle)
    have hcount := run.fetches
    rw [← hprefix] at hcount
    have hlen : (run.input.appendRequest request).requests.length =
        run.input.requests.length + 1 := by
      simp [Instance.appendRequest]
    rw [← hnew, hlen]
    omega
  · exact mul_pos hcpos run.nextSlopePos
  · intro d
    simp only [Instance.appendRequest, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, hreqdelay, hreqarrival]
    rw [hsumOld d, hsumNow, add_tsub_comm harrle d, ← hudef]
    ring
  · calc run.slopeTotal + run.nextSlope
        ≤ ε * run.nextSlope + run.nextSlope := by gcongr; exact run.slopeTotalLe
      _ = (ε + 1) * run.nextSlope := by ring
      _ ≤ (ε * c) * run.nextSlope := by gcongr
      _ = ε * (c * run.nextSlope) := by ring
  · calc run.used + rate * gap + run.budget / 2
        ≤ run.used + run.budget / 2 + run.budget / 2 := by gcongr
      _ = run.used + run.budget := by rw [add_assoc, add_halves]
      _ ≤ 1 := run.budgetTotal
  · rw [← hnew, htotalDelay]
    simp only [Instance.appendRequest, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, hreqdelay, hreqarrival, ← hudef]
    rw [hsumNow]
    calc (run.input.requests.map fun r => r.delay (run.now - r.arrival)).sum +
          run.slopeTotal * w + run.nextSlope * u
        ≤ ((1 + ε) * old.totalDelay run.input + run.used) + (ε * run.nextSlope) * w +
            run.nextSlope * u := by gcongr; exacts [run.delayBound, run.slopeTotalLe]
      _ = (1 + ε) * (old.totalDelay run.input + run.nextSlope * u) +
            (run.used + rate * gap) := by rw [hwu, hrate]; ring

end
end PagingWithDelay.GeneralLowerBound
