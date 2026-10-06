import Proofs.EventLoop.PendingThreshold

/-!
# The two triggers

Both triggers fetch a pending page when its accumulated delay reaches a level:
the threshold `δ` for `Trigger.threshold δ`, and `0` for `Trigger.deadline`,
which fetches at the last moment the delay of every pending request is still
zero.  This file proves that the due time attains that level
(`Trigger.dueTime_value`), which is all the event-loop invariants need to know
about the trigger, and the facts about deadlines the deadline trigger rests on.
-/

namespace PagingWithDelay

/-! ## Deadlines of requests -/

namespace Request

variable {Page : Type*}

private theorem positiveSet_nonempty (request : Request Page) :
    {wait | 0 < request.delay wait}.Nonempty := by
  obtain ⟨wait, hwait⟩ := request.delay_unbounded 1
  exact ⟨wait, zero_lt_one.trans_le hwait⟩

/-- Up to its deadline a request has no delay. -/
theorem delay_eq_zero_of_le_deadline (request : Request Page) {t : Time}
    (ht : t ≤ request.deadline) : request.delay (t - request.arrival) = 0 := by
  set W := sInf {wait | 0 < request.delay wait} with hW
  have hwait : t - request.arrival ≤ W := tsub_le_iff_left.mpr ht
  -- below `W` the delay is zero, and the zero set is closed
  have hzero : Set.Icc 0 W ⊆ request.delay ⁻¹' {0} := by
    rcases eq_or_lt_of_le (zero_le W) with heq | hlt
    · intro w hw
      have : w = 0 := le_antisymm (heq ▸ hw.2) hw.1
      simp [this, request.delay_zero]
    · rw [← closure_Ico hlt.ne]
      refine (isClosed_singleton.preimage request.delay_continuous).closure_subset_iff.mpr ?_
      intro w hw
      by_contra hne
      have hmem : w ∈ {wait | 0 < request.delay wait} := pos_iff_ne_zero.mpr hne
      exact absurd (csInf_le ⟨0, fun _ _ => zero_le _⟩ hmem) (not_le.mpr hw.2)
  exact hzero ⟨zero_le _, hwait⟩

/-- After its deadline a request has positive delay. -/
theorem delay_pos_of_deadline_lt (request : Request Page) {t : Time}
    (ht : request.deadline < t) : 0 < request.delay (t - request.arrival) := by
  have hlt : sInf {wait | 0 < request.delay wait} < t - request.arrival :=
    lt_tsub_iff_left.mpr ht
  obtain ⟨wait, hwait, hle⟩ := exists_lt_of_csInf_lt (positiveSet_nonempty request) hlt
  exact hwait.trans_le (request.delay_mono hle.le)

/-- A request without delay at `t` has its deadline no earlier than `t`. -/
theorem le_deadline_of_delay_eq_zero (request : Request Page) {t : Time}
    (ht : request.delay (t - request.arrival) = 0) : t ≤ request.deadline := by
  by_contra hlt
  exact (request.delay_pos_of_deadline_lt (not_le.mp hlt)).ne' ht

end Request

namespace FIFO

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-! ## The deadline trigger -/

/-- The times at which a pending request for `page` has reached its deadline. -/
private theorem deadlineSet_closed (state : State Page) (page : Page) :
    IsClosed {t : Time | state.now ≤ t ∧ ∃ occurrence ∈ state.pending,
      occurrence.request.page = page ∧ occurrence.request.deadline ≤ t} := by
  have heq : {t : Time | ∃ occurrence ∈ state.pending,
        occurrence.request.page = page ∧ occurrence.request.deadline ≤ t} =
      ⋃ occurrence ∈ {o | o ∈ state.pending ∧ o.request.page = page},
        Set.Ici occurrence.request.deadline := by
    ext t
    simp [and_assoc]
  have hclosed : IsClosed {t : Time | ∃ occurrence ∈ state.pending,
      occurrence.request.page = page ∧ occurrence.request.deadline ≤ t} := by
    rw [heq]
    exact ((List.finite_toSet state.pending).subset fun o ho => ho.1).isClosed_biUnion
      fun _ _ => isClosed_Ici
  exact isClosed_Ici.inter hclosed

private theorem deadlineSet_nonempty {state : State Page} {page : Page}
    (hpending : ∃ occurrence ∈ state.pending, occurrence.request.page = page) :
    {t : Time | state.now ≤ t ∧ ∃ occurrence ∈ state.pending,
      occurrence.request.page = page ∧ occurrence.request.deadline ≤ t}.Nonempty := by
  obtain ⟨occurrence, hmem, hpage⟩ := hpending
  exact ⟨max state.now occurrence.request.deadline, le_max_left _ _,
    occurrence, hmem, hpage, le_max_right _ _⟩

theorem deadlineTime_ge_now (state : State Page) (page : Page)
    (hpending : ∃ occurrence ∈ state.pending, occurrence.request.page = page) :
    state.now ≤ deadlineTime state page :=
  le_csInf (deadlineSet_nonempty hpending) fun _ ht => ht.1

/-- At its deadline time some pending request for the page has reached its
deadline. -/
theorem exists_deadline_le_deadlineTime (state : State Page) (page : Page)
    (hpending : ∃ occurrence ∈ state.pending, occurrence.request.page = page) :
    ∃ occurrence ∈ state.pending, occurrence.request.page = page ∧
      occurrence.request.deadline ≤ deadlineTime state page :=
  ((deadlineSet_closed state page).csInf_mem (deadlineSet_nonempty hpending)
    ⟨0, fun _ _ => zero_le _⟩).2

/-- Any instant after `now` at which a pending request for the page has reached
its deadline bounds the deadline time. -/
theorem deadlineTime_le {state : State Page} {page : Page} {instant : Time}
    (hnow : state.now ≤ instant) {occurrence : Occurrence Page}
    (hmem : occurrence ∈ state.pending) (hpage : occurrence.request.page = page)
    (hdeadline : occurrence.request.deadline ≤ instant) :
    deadlineTime state page ≤ instant :=
  csInf_le ⟨0, fun _ _ => zero_le _⟩ ⟨hnow, occurrence, hmem, hpage, hdeadline⟩

/-- No pending request has positive delay at the deadline time, if none has
now. -/
theorem deadlineTime_value (state : State Page) (page : Page)
    (hnow : pendingCost state page state.now ≤ 0) :
    pendingCost state page (deadlineTime state page) = 0 := by
  have hzero : ∀ occurrence ∈ state.pending.filter (fun o => o.request.page = page),
      occurrence.request.delay (state.now - occurrence.request.arrival) = 0 := by
    intro occurrence ho
    have hsum : pendingCost state page state.now = 0 := le_antisymm hnow (zero_le _)
    unfold pendingCost at hsum
    exact List.sum_eq_zero_iff.mp hsum _ (List.mem_map_of_mem ho)
  unfold pendingCost
  refine List.sum_eq_zero fun cost hcost => ?_
  obtain ⟨occurrence, ho, rfl⟩ := List.mem_map.mp hcost
  obtain ⟨hmem, hpage⟩ := List.mem_filter.mp ho
  exact occurrence.request.delay_eq_zero_of_le_deadline <| deadlineTime_le
    (occurrence.request.le_deadline_of_delay_eq_zero (hzero occurrence ho)) hmem
    (of_decide_eq_true hpage) le_rfl

/-- Strictly after its deadline time a pending page has positive pending cost. -/
theorem pendingCost_pos_of_deadlineTime_lt (state : State Page) (page : Page)
    (hpending : ∃ occurrence ∈ state.pending, occurrence.request.page = page)
    {t : Time} (ht : deadlineTime state page < t) :
    0 < pendingCost state page t := by
  obtain ⟨occurrence, hmem, hpage, hdeadline⟩ :=
    exists_deadline_le_deadlineTime state page hpending
  exact (occurrence.request.delay_pos_of_deadline_lt (hdeadline.trans_lt ht)).trans_le
    (delay_le_pendingCost hmem hpage t)

/-! ## Both triggers -/

/-- The delay level at which a trigger fires: `δ`, or `0` for deadlines. -/
def Trigger.level : Trigger → Cost
  | .threshold δ => δ
  | .deadline => 0

@[simp] theorem Trigger.level_threshold (δ : Cost) : (Trigger.threshold δ).level = δ := rfl
@[simp] theorem Trigger.level_deadline : Trigger.deadline.level = 0 := rfl
@[simp] theorem Trigger.dueTime_threshold (δ : Cost) :
    (Trigger.threshold δ).dueTime (Page := Page) = thresholdTime δ := rfl
@[simp] theorem Trigger.dueTime_deadline :
    Trigger.deadline.dueTime (Page := Page) = deadlineTime := rfl

/-- The due time attains the trigger's level. -/
theorem Trigger.dueTime_value (trigger : Trigger) (state : State Page) (page : Page)
    (hpending : ∃ occurrence ∈ state.pending, occurrence.request.page = page)
    (hnow : pendingCost state page state.now ≤ trigger.level) :
    pendingCost state page (trigger.dueTime state page) = trigger.level := by
  cases trigger with
  | threshold δ => exact thresholdTime_value state page hpending hnow
  | deadline => exact deadlineTime_value state page hnow

theorem selectedPayment_value {trigger : Trigger} {state : State Page} {time : Time}
    {page : Page} (hselected : nextPayment? trigger state = some (time, page))
    (hnow : pendingCost state page state.now ≤ trigger.level) :
    pendingCost state page time = trigger.level := by
  rw [← nextPayment_time_eq hselected]
  exact trigger.dueTime_value state page (nextPayment_pending hselected) hnow

/-- A pending page is never due before `now`. -/
theorem Trigger.dueTime_ge_now (trigger : Trigger) (state : State Page) (page : Page)
    (hpending : ∃ occurrence ∈ state.pending, occurrence.request.page = page) :
    state.now ≤ trigger.dueTime state page := by
  cases trigger with
  | threshold δ => exact thresholdTime_ge_now state page hpending
  | deadline => exact deadlineTime_ge_now state page hpending

/-- A selected payment is not before `now`. -/
theorem nextPayment_now_le {trigger : Trigger} {state : State Page} {time : Time} {page : Page}
    (hselected : nextPayment? trigger state = some (time, page)) : state.now ≤ time :=
  nextPayment_time_eq hselected ▸ trigger.dueTime_ge_now state page (nextPayment_pending hselected)

end

end FIFO

end PagingWithDelay
