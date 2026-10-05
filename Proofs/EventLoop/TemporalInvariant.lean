import Proofs.EventLoop.PendingThreshold
import Proofs.EventLoop.PaymentAccounting

namespace PagingWithDelay.FIFO
variable {Page : Type*} [DecidableEq Page] {δ : Cost}
noncomputable section

/-- No pending page has yet accumulated the threshold `δ`. -/
def BelowThreshold (δ : Cost) (state : State Page) : Prop :=
  ∀ page, (∃ occurrence ∈ state.pending, occurrence.request.page = page) →
    pendingCost state page state.now ≤ δ

theorem initial_belowThreshold (input : Instance Page) :
    BelowThreshold δ (initialState input) := by
  intro page h; simp [initialState] at h

theorem mem_eraseDups_of_mem (x : Page) : ∀ xs : List Page,
    x ∈ xs → x ∈ xs.eraseDups := by
  intro xs hx
  have loop : ∀ (as bs : List Page), x ∈ as ∨ x ∈ bs →
      x ∈ List.eraseDupsBy.loop (fun a b : Page => a == b) as bs := by
    intro as
    induction as with
    | nil => intro bs h; simpa [List.eraseDupsBy.loop] using h
    | cons head tail ih =>
        intro bs h
        simp only [List.eraseDupsBy.loop]
        split
        · rename_i hdup
          apply ih bs
          rcases h with h | h
          · simp only [List.mem_cons] at h
            rcases h with rfl | h
            · apply Or.inr
              rw [List.any_eq_true] at hdup
              obtain ⟨b, hb, hxb⟩ := hdup
              have : x = b := of_decide_eq_true hxb
              simpa [this] using hb
            · exact Or.inl h
          · exact Or.inr h
        · rename_i hdup
          apply ih (head :: bs)
          rcases h with h | h
          · simp only [List.mem_cons] at h
            rcases h with rfl | h
            · exact Or.inr (by simp)
            · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem head h)
  change x ∈ List.eraseDupsBy.loop (fun a b : Page => a == b) xs []
  exact loop xs [] (Or.inl hx)

theorem nextPayment_exists_of_pending {state : State Page} {page : Page}
    (hpage : ∃ occurrence ∈ state.pending, occurrence.request.page = page) :
    ∃ time selected, nextPayment? δ state = some (time, selected) := by
  have hm : page ∈ pendingPages state := by
    unfold pendingPages
    apply mem_eraseDups_of_mem
    simpa only [List.mem_map] using hpage
  unfold nextPayment?
  cases h : (pendingPages state).map (fun p => (thresholdTime δ state p, p)) with
  | nil =>
      have he : pendingPages state = [] := List.map_eq_nil_iff.mp h
      simp [he] at hm
  | cons head tail =>
      refine ⟨(tail.foldl earlierPayment head).1,
        (tail.foldl earlierPayment head).2, ?_⟩
      simp only [List.foldl_cons]
      have aux : ∀ (xs : List (Time × Page)) best,
          xs.foldl
            (fun current candidate => some (match current with
              | none => candidate
              | some current => earlierPayment current candidate))
            (some best) = some (xs.foldl earlierPayment best) := by
        intro xs
        induction xs with
        | nil => intro best; rfl
        | cons x xs ih => intro best; simp only [List.foldl_cons]; exact ih _
      exact aux tail head

theorem nextAction_payment_selected {state : State Page} {time : Time} {page : Page}
    (h : nextAction? δ state = some (.payment time page)) :
    nextPayment? δ state = some (time, page) := by
  unfold nextAction? at h
  cases hu : state.unseen with
  | nil =>
      cases hp : nextPayment? δ state with
      | none => simp [hu, hp] at h
      | some pair =>
          rcases pair with ⟨t, p⟩
          simp only [hu, hp] at h
          cases h
          rfl
  | cons occurrence unseen =>
      cases hp : nextPayment? δ state with
      | none => simp [hu, hp] at h
      | some pair =>
          rcases pair with ⟨t, p⟩
          simp only [hu, hp] at h
          split at h
          · simp at h
          · cases h
            rfl

private theorem arrival_le_thresholdTime {state : State Page} {occurrence : Occurrence Page}
    (ha : nextAction? δ state = some (.arrival occurrence))
    {page : Page} (hpage : ∃ o ∈ state.pending, o.request.page = page) :
    occurrence.request.arrival ≤ thresholdTime δ state page := by
  obtain ⟨time, selected, hp⟩ := nextPayment_exists_of_pending (δ := δ) hpage
  have hm : page ∈ pendingPages state := by
    unfold pendingPages
    apply mem_eraseDups_of_mem
    simpa only [List.mem_map] using hpage
  have hat : occurrence.request.arrival ≤ time := by
    unfold nextAction? at ha
    cases hu : state.unseen with
    | nil => simp [hu, hp] at ha
    | cons head tail =>
        simp only [hu, hp] at ha
        split at ha
        · injection ha with heq; cases heq; assumption
        · simp at ha
  exact hat.trans (nextPayment_time_le_thresholdTime hp hm)

private theorem pendingCost_append_arrival
    (state : State Page) (occurrence : Occurrence Page) (page : Page) :
    pendingCost ({ state with
        now := occurrence.request.arrival
        unseen := state.unseen.tail
        pending := state.pending ++ [occurrence]} : State Page)
      page occurrence.request.arrival = pendingCost state page occurrence.request.arrival := by
  unfold pendingCost
  simp only [List.filter_append, List.map_append, List.sum_append]
  by_cases h : occurrence.request.page = page
  · simp [h, occurrence.request.delay_zero]
  · simp [h]

theorem step_belowThreshold (input : Instance Page)
    (state : State Page) (action : Action Page)
    (hinv : BelowThreshold δ state)
    (haction : nextAction? δ state = some action) :
    BelowThreshold δ (step input state action) := by
  cases action with
  | arrival occurrence =>
      intro page hafter
      by_cases hhit : occurrence.request.page ∈ state.queue
      · simp only [step, hhit, if_pos] at hafter ⊢
        have hle := arrival_le_thresholdTime haction hafter
        exact (pendingCost_monotone state page hle).trans_eq
          (thresholdTime_value state page hafter (hinv page hafter))
      · simp only [step, hhit] at hafter ⊢
        change pendingCost
          ({ state with
             now := occurrence.request.arrival
             unseen := state.unseen.tail
             pending := state.pending ++ [occurrence] } : State Page)
          page occurrence.request.arrival ≤ δ
        have holdOrNew :
            (∃ o ∈ state.pending, o.request.page = page) ∨
              occurrence.request.page = page := by
          obtain ⟨o, ho, heq⟩ := hafter
          simp at ho
          rcases ho with ho | rfl
          · exact Or.inl ⟨o, ho, heq⟩
          · exact Or.inr heq
        rw [pendingCost_append_arrival]
        rcases holdOrNew with hold | hnew
        · have hle := arrival_le_thresholdTime haction hold
          exact (pendingCost_monotone state page hle).trans_eq
            (thresholdTime_value state page hold (hinv page hold))
        · by_cases hold : ∃ o ∈ state.pending, o.request.page = page
          · have hle := arrival_le_thresholdTime haction hold
            exact (pendingCost_monotone state page hle).trans_eq
              (thresholdTime_value state page hold (hinv page hold))
          · unfold pendingCost
            have hempty : state.pending.filter (fun o => o.request.page = page) = [] := by
              apply List.eq_nil_iff_forall_not_mem.mpr
              intro o ho
              exact hold ⟨o, (List.mem_filter.mp ho).1,
                of_decide_eq_true (List.mem_filter.mp ho).2⟩
            simp [hempty]
  | payment time paid =>
      have hp := nextAction_payment_selected haction
      intro candidate hafter
      simp only [step] at hafter ⊢
      have hold : ∃ o ∈ state.pending, o.request.page = candidate := by
        obtain ⟨o, ho, heq⟩ := hafter
        exact ⟨o, (List.mem_filter.mp ho).1, heq⟩
      have hne : candidate ≠ paid := by
        intro heq; subst candidate
        obtain ⟨o, ho, heq⟩ := hafter
        exact (of_decide_eq_true (List.mem_filter.mp ho).2) heq
      have hm : candidate ∈ pendingPages state := by
        unfold pendingPages
        apply mem_eraseDups_of_mem
        simpa only [List.mem_map] using hold
      have hcost : pendingCost state candidate time ≤ δ := by
        exact (pendingCost_monotone state candidate
          (nextPayment_time_le_thresholdTime hp hm)).trans_eq
            (thresholdTime_value state candidate hold (hinv candidate hold))
      unfold pendingCost at hcost ⊢
      simp only [List.filter_filter]
      convert hcost using 1
      apply congrArg (fun xs : List (Occurrence Page) => (xs.map fun occurrence =>
        occurrence.request.delay (time - occurrence.request.arrival)).sum)
      apply List.filter_congr
      intro o ho
      show (decide (o.request.page = candidate) && decide (o.request.page ≠ paid)) =
        decide (o.request.page = candidate)
      by_cases hoc : o.request.page = candidate
      · simp [hoc, hne]
      · simp [hoc]

theorem selected_payment_delayCost
    (state : State Page) (time : Time) (page : Page)
    (hinv : BelowThreshold δ state)
    (haction : nextAction? δ state = some (.payment time page)) :
    Payment.delayCost
      { time := time, page := page,
        served := state.pending.filter fun o => o.request.page = page,
        queueAfter := [] } = δ := by
  rw [payment_delayCost_mk_eq_pendingCost]
  have hp := nextAction_payment_selected haction
  exact selectedPayment_value hp
    (hinv page (pending_of_mem_pendingPages (nextPayment_mem_pendingPages hp)))

/-- Every payment made so far carries exactly the threshold `δ` of delay. -/
def ThresholdPayments (δ : Cost) (state : State Page) : Prop :=
  ∀ payment ∈ state.payments, payment.delayCost = δ

theorem initial_thresholdPayments (input : Instance Page) :
    ThresholdPayments δ (initialState input) := by simp [ThresholdPayments, initialState]

theorem run_invariants (input : Instance Page) :
    ∀ fuel state, BelowThreshold δ state → ThresholdPayments δ state →
      BelowThreshold δ (run δ input fuel state) ∧ ThresholdPayments δ (run δ input fuel state) := by
  intro fuel
  induction fuel with
  | zero => exact fun state hb hu => ⟨hb, hu⟩
  | succ fuel ih =>
      intro state hb hu
      rw [run]
      cases ha : nextAction? δ state with
      | none => exact ⟨hb, hu⟩
      | some action =>
          apply ih
          · exact step_belowThreshold input state action hb ha
          · cases action with
            | arrival occurrence => simpa [ThresholdPayments, step] using hu
            | payment time page =>
                intro payment hmem
                simp only [step, List.mem_append, List.mem_singleton] at hmem
                rcases hmem with hold | rfl
                · exact hu payment hold
                · exact selected_payment_delayCost state time page hb ha

theorem final_thresholdPayments (input : Instance Page) :
    ThresholdPayments δ (run δ input (2 * input.requests.length) (initialState input)) :=
  (run_invariants input _ _ (initial_belowThreshold input)
    (initial_thresholdPayments input)).2

end
end PagingWithDelay.FIFO
