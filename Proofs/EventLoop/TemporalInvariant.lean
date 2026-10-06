import Proofs.EventLoop.Trigger
import Proofs.EventLoop.PaymentAccounting

namespace PagingWithDelay.FIFO
variable {Page : Type*} [DecidableEq Page] {trigger : Trigger}
noncomputable section

/-- No pending page has yet accumulated more than the level `δ` (`0` for deadlines). -/
def BelowThreshold (δ : Cost) (state : State Page) : Prop :=
  ∀ page, (∃ occurrence ∈ state.pending, occurrence.request.page = page) →
    pendingCost state page state.now ≤ δ

theorem initial_belowThreshold (input : Instance Page) :
    BelowThreshold trigger.level (initialState input) := by
  intro page h; simp [initialState] at h

/-- Arrivals come no later than the due time of any pending page. -/
private theorem arrival_le_dueTime {state : State Page} {occurrence : Occurrence Page}
    (ha : nextAction? trigger state = some (.arrival occurrence))
    {page : Page} (hpage : ∃ o ∈ state.pending, o.request.page = page) :
    occurrence.request.arrival ≤ trigger.dueTime state page := by
  obtain ⟨time, selected, hp⟩ := nextPayment_exists_of_pending (trigger := trigger) hpage
  exact ((nextAction_arrival ha).2 time selected hp).trans
    (nextPayment_time_le_dueTime hp (mem_pendingPages.2 hpage))

/-- Up to its due time, a page has accumulated at most the level. -/
private theorem pendingCost_le_level {state : State Page}
    (hinv : BelowThreshold trigger.level state) {page : Page} {t : Time}
    (ht : (∃ o ∈ state.pending, o.request.page = page) → t ≤ trigger.dueTime state page) :
    pendingCost state page t ≤ trigger.level := by
  by_cases hpending : ∃ o ∈ state.pending, o.request.page = page
  · exact (pendingCost_monotone state page (ht hpending)).trans_eq
      (trigger.dueTime_value state page hpending (hinv page hpending))
  · push_neg at hpending
    have hnil : state.pending.filter (fun o => o.request.page = page) = [] :=
      List.filter_eq_nil_iff.2 fun o ho => by simpa using hpending o ho
    simp [pendingCost, hnil]

theorem step_belowThreshold (input : Instance Page)
    (state : State Page) (action : Action Page)
    (hinv : BelowThreshold trigger.level state)
    (haction : nextAction? trigger state = some action) :
    BelowThreshold trigger.level (step input state action) := by
  intro page hafter
  cases action with
  | arrival occurrence =>
      -- the arriving request has no delay yet
      have hcost : pendingCost (step input state (.arrival occurrence)) page
          occurrence.request.arrival = pendingCost state page occurrence.request.arrival := by
        simp only [step, pendingCost]
        split
        · rfl
        · by_cases h : occurrence.request.page = page <;> simp [h, occurrence.request.delay_zero]
      change pendingCost _ page occurrence.request.arrival ≤ _
      rw [hcost]
      exact pendingCost_le_level hinv (arrival_le_dueTime haction)
  | payment time paid =>
      -- the paid page is no longer pending; the others keep their pending requests
      have hne : page ≠ paid := by
        obtain ⟨o, ho, rfl⟩ := hafter
        simpa using (List.mem_filter.1 ho).2
      have hcost : pendingCost (step input state (.payment time paid)) page time =
          pendingCost state page time := by
        simp only [step, pendingCost, List.filter_filter]
        congr 2
        apply List.filter_congr
        intro o _
        by_cases h : o.request.page = page <;> simp [h, hne]
      change pendingCost _ page time ≤ _
      rw [hcost]
      exact pendingCost_le_level hinv fun hpending =>
        nextPayment_time_le_dueTime (nextAction_payment_selected haction)
          (mem_pendingPages.2 hpending)

theorem Reachable.belowThreshold {input : Instance Page} {state : State Page}
    (h : Reachable trigger input state) : BelowThreshold trigger.level state := by
  induction h with
  | initial => exact initial_belowThreshold input
  | step _ ha ih => exact step_belowThreshold input _ _ ih ha

/-- Every payment made so far carries exactly the level `δ` of delay. -/
def ThresholdPayments (δ : Cost) (state : State Page) : Prop :=
  ∀ payment ∈ state.payments, payment.delayCost = δ

theorem Reachable.thresholdPayments {input : Instance Page} {state : State Page}
    (h : Reachable trigger input state) : ThresholdPayments trigger.level state := by
  induction h with
  | initial => simp [ThresholdPayments, initialState]
  | @step state action hr ha ih =>
      cases action with
      | arrival occurrence => simpa [ThresholdPayments, FIFO.step] using ih
      | payment time page =>
          intro payment hmem
          simp only [FIFO.step, List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hold | rfl
          · exact ih payment hold
          · have hp := nextAction_payment_selected ha
            rw [payment_delayCost_mk_eq_pendingCost]
            exact selectedPayment_value hp (hr.belowThreshold page (nextPayment_pending hp))

theorem final_thresholdPayments (input : Instance Page) :
    ThresholdPayments trigger.level (run trigger input (2 * input.requests.length) (initialState input)) :=
  (reachable_final input).thresholdPayments

end
end PagingWithDelay.FIFO

/-! ## Payments serve their page, and deadline payments are due

Every payment serves at least one request.  With the deadline trigger, strictly
after a payment the requests it served have positive delay: the payment is made
at the earliest deadline of the requests it serves. -/

namespace PagingWithDelay.FIFO
variable {Page : Type*} [DecidableEq Page] {trigger : Trigger}
noncomputable section

/-- Delay the occurrences served by a payment would have accrued at `t`. -/
def Payment.delayCostAt (payment : Payment Page) (t : Time) : Cost :=
  (payment.served.map fun occurrence =>
    occurrence.request.delay (t - occurrence.request.arrival)).sum

/-- Every payment made so far serves at least one request, and, for the deadline
trigger, serves requests whose delay is positive strictly after the payment. -/
structure DuePayments (trigger : Trigger) (state : State Page) : Prop where
  served_ne_nil : ∀ payment ∈ state.payments, payment.served ≠ []
  due : trigger = .deadline →
    ∀ payment ∈ state.payments, ∀ t, payment.time < t → 0 < payment.delayCostAt t

theorem Reachable.duePayments {input : Instance Page} {state : State Page}
    (h : Reachable trigger input state) : DuePayments trigger state := by
  induction h with
  | initial => exact ⟨by simp [initialState], by simp [initialState]⟩
  | @step state action _ ha ih =>
      cases action with
      | arrival occurrence => exact ⟨ih.served_ne_nil, ih.due⟩
      | payment time page =>
          have hp := nextAction_payment_selected ha
          have hpending := nextPayment_pending hp
          constructor
          · intro payment hmem
            simp only [FIFO.step, List.mem_append, List.mem_singleton] at hmem
            rcases hmem with hold | rfl
            · exact ih.served_ne_nil payment hold
            · obtain ⟨occurrence, ho, hpage⟩ := hpending
              exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨ho, by simpa using hpage⟩)
          · intro hdeadline payment hmem t ht
            simp only [FIFO.step, List.mem_append, List.mem_singleton] at hmem
            rcases hmem with hold | rfl
            · exact ih.due hdeadline payment hold t ht
            · subst hdeadline
              rw [← nextPayment_time_eq hp] at ht
              exact pendingCost_pos_of_deadlineTime_lt state page hpending ht

theorem final_duePayments (input : Instance Page) :
    DuePayments trigger (run trigger input (2 * input.requests.length) (initialState input)) :=
  (reachable_final input).duePayments

end
end PagingWithDelay.FIFO
