import PagingWithDelay.EventLoop.TemporalInvariant

namespace PagingWithDelay.FIFO

open Set

variable {Page : Type*} [DecidableEq Page] {δ : Cost}

noncomputable section

/-- The order information carried by a reachable event-loop state. -/
structure TimeInvariant (state : State Page) : Prop where
  payments_chronological : state.payments.Pairwise fun earlier later =>
    earlier.time ≤ later.time
  payments_before_now : ∀ payment ∈ state.payments, payment.time ≤ state.now
  unseen_chronological : state.unseen.Pairwise fun earlier later =>
    earlier.request.arrival ≤ later.request.arrival
  now_before_unseen : ∀ occurrence ∈ state.unseen,
    state.now ≤ occurrence.request.arrival

theorem initial_timeInvariant (input : Instance Page) (valid : input.Valid) :
    TimeInvariant (initialState input) := by
  have enumerate_authentic : ∀ (n : ℕ) (requests : List (Request Page))
      (occurrence : Occurrence Page), occurrence ∈ enumerateFrom n requests →
        occurrence.request ∈ requests := by
    intro n requests occurrence h
    induction requests generalizing n with
    | nil => simp [enumerateFrom] at h
    | cons head tail ih =>
        simp only [enumerateFrom, List.mem_cons] at h ⊢
        rcases h with rfl | h
        · exact Or.inl rfl
        · exact Or.inr (ih (n + 1) h)
  have enumerate_pairwise : ∀ (n : ℕ) (requests : List (Request Page)),
      requests.Pairwise (fun earlier later => earlier.arrival ≤ later.arrival) →
      (enumerateFrom n requests).Pairwise fun earlier later =>
        earlier.request.arrival ≤ later.request.arrival := by
    intro n requests h
    induction requests generalizing n with
    | nil => simp [enumerateFrom]
    | cons head tail ih =>
        rw [List.pairwise_cons] at h
        simp only [enumerateFrom, List.pairwise_cons]
        constructor
        · intro occurrence hocc
          have request_mem := enumerate_authentic (n + 1) tail occurrence hocc
          exact h.1 occurrence.request request_mem
        · exact ih (n + 1) h.2
  constructor
  · simp [initialState]
  · simp [initialState]
  · simpa [initialState, enumerate] using
      enumerate_pairwise 0 input.requests valid.chronological
  · intro occurrence h
    exact bot_le

theorem thresholdTime_ge_now (state : State Page) (page : Page)
    (hpending : ∃ occurrence ∈ state.pending,
      occurrence.request.page = page) :
    state.now ≤ thresholdTime δ state page := by
  let S : Set Time := {t | state.now ≤ t ∧ δ ≤ pendingCost state page t}
  have hnonempty : S.Nonempty := by
    obtain ⟨occurrence, hmem, heq⟩ := hpending
    obtain ⟨wait, hwait⟩ := occurrence.request.delay_unbounded δ
    let t := state.now + occurrence.request.arrival + wait
    refine ⟨t, ?_, ?_⟩
    · exact le_add_right (le_add_right le_rfl)
    · unfold pendingCost
      calc
        δ ≤ occurrence.request.delay (t - occurrence.request.arrival) :=
          hwait.trans (occurrence.request.delay_mono (by
            change wait ≤ (state.now + occurrence.request.arrival + wait) -
              occurrence.request.arrival
            rw [add_comm state.now occurrence.request.arrival, add_assoc,
              add_tsub_cancel_left]
            exact le_add_left le_rfl))
        _ ≤ _ := by
          apply List.single_le_sum
          · intro cost _
            exact bot_le
          · simp only [List.mem_map]
            refine ⟨occurrence, ?_, rfl⟩
            simp only [List.mem_filter]
            exact ⟨hmem, by simp [heq]⟩
  have hclosed : IsClosed S := by
    simpa [S] using isClosed_Ici.inter
      (isClosed_Ici.preimage (pendingCost_continuous state page))
  have hbdd : BddBelow S := ⟨0, fun _ _ => bot_le⟩
  exact (hclosed.csInf_mem hnonempty hbdd).1

theorem step_timeInvariant (input : Instance Page)
    (state : State Page) (action : Action Page)
    (htime : TimeInvariant state)
    (haction : nextAction? δ state = some action) :
    TimeInvariant (step input state action) := by
  cases action with
  | arrival occurrence =>
      have hunseen : state.unseen = occurrence :: state.unseen.tail := by
        unfold nextAction? at haction
        cases h : state.unseen with
        | nil =>
            cases hp : nextPayment? δ state <;> simp [h, hp] at haction
        | cons head tail =>
            cases hp : nextPayment? δ state <;> simp only [h, hp] at haction
            · injection haction with heq
              cases heq
              simp_all
            · split at haction
              · injection haction with heq
                cases heq
                simp_all
              · simp at haction
      have hnow : state.now ≤ occurrence.request.arrival := by
        apply htime.now_before_unseen occurrence
        rw [hunseen]
        simp
      constructor
      · exact htime.payments_chronological
      · intro payment hp
        exact (htime.payments_before_now payment hp).trans hnow
      · simpa only [step] using htime.unseen_chronological.tail
      · intro later hlater
        simp only [step] at hlater ⊢
        have hpw := htime.unseen_chronological
        rw [hunseen, List.pairwise_cons] at hpw
        exact hpw.1 later hlater
  | payment time page =>
      have hselected := nextAction_payment_selected haction
      have hpending := pending_of_mem_pendingPages
        (nextPayment_mem_pendingPages hselected)
      have hnow : state.now ≤ time := by
        rw [← nextPayment_time_eq hselected]
        exact thresholdTime_ge_now state page hpending
      constructor
      · simp only [step]
        rw [List.pairwise_append]
        refine ⟨htime.payments_chronological, by simp, ?_⟩
        intro old hold new hnew
        simp only [List.mem_singleton] at hnew
        subst new
        exact (htime.payments_before_now old hold).trans hnow
      · intro candidate hcand
        simp only [step, List.mem_append, List.mem_singleton] at hcand
        rcases hcand with hold | rfl
        · exact (htime.payments_before_now candidate hold).trans hnow
        · exact le_rfl
      · exact htime.unseen_chronological
      · intro occurrence hocc
        have hoccState : occurrence ∈ state.unseen := by
          simpa only [step] using hocc
        unfold nextAction? at haction
        cases hu : state.unseen with
        | nil => simp [hu] at hoccState
        | cons head tail =>
            cases hp : nextPayment? δ state with
            | none => simp [hu, hp] at haction
            | some pair =>
                rcases pair with ⟨selectedTime, selectedPage⟩
                simp only [hu, hp] at haction
                split at haction
                · simp at haction
                · injection haction with hpair
                  cases hpair
                  have hhead : time ≤ head.request.arrival := le_of_not_ge (by assumption)
                  rw [hu] at hoccState
                  simp only [List.mem_cons] at hoccState
                  rcases hoccState with rfl | htail
                  · exact hhead
                  · have hpw := htime.unseen_chronological
                    rw [hu, List.pairwise_cons] at hpw
                    exact hhead.trans (hpw.1 occurrence htail)

theorem run_timeInvariant (input : Instance Page) :
    ∀ fuel state, TimeInvariant state → BelowThreshold δ state →
      TimeInvariant (run δ input fuel state) := by
  intro fuel
  induction fuel with
  | zero => exact fun _ htime _ => htime
  | succ fuel ih =>
      intro state htime hbelow
      rw [run]
      cases ha : nextAction? δ state with
      | none => exact htime
      | some action =>
          exact ih _ (step_timeInvariant input state action htime ha)
            (step_belowThreshold input state action hbelow ha)

theorem final_payment_times_chronological (input : Instance Page)
    (valid : input.Valid) :
    (run δ input (2 * input.requests.length) (initialState input)).payments.Pairwise
      fun earlier later => earlier.time ≤ later.time :=
  (run_timeInvariant input _ _ (initial_timeInvariant input valid)
    (initial_belowThreshold input)).payments_chronological

end

end PagingWithDelay.FIFO
