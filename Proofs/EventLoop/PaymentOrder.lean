import Proofs.EventLoop.TemporalInvariant

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page] {trigger : Trigger}

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

theorem initial_timeInvariant (input : Instance Page) :
    TimeInvariant (initialState input) where
  payments_chronological := by simp [initialState]
  payments_before_now := by simp [initialState]
  unseen_chronological := by
    have := input.chronological
    rw [← enumerate_map_request input.requests, List.pairwise_map] at this
    exact this
  now_before_unseen := fun _ _ => bot_le

/-- A payment comes strictly before every request still to arrive. -/
theorem payment_lt_unseen {state : State Page} {time : Time} {page : Page}
    (htime : TimeInvariant state) (ha : nextAction? trigger state = some (.payment time page))
    {occurrence : Occurrence Page} (ho : occurrence ∈ state.unseen) :
    time < occurrence.request.arrival := by
  have hhead := (nextAction_payment ha).2
  have hchron := htime.unseen_chronological
  cases hu : state.unseen with
  | nil => simp [hu] at ho
  | cons head tail =>
      rw [hu] at ho hchron hhead
      rcases List.mem_cons.mp ho with rfl | htail
      · exact hhead _ rfl
      · exact (hhead head rfl).trans_le (List.rel_of_pairwise_cons hchron htail)

theorem step_timeInvariant (input : Instance Page)
    (state : State Page) (action : Action Page)
    (htime : TimeInvariant state)
    (haction : nextAction? trigger state = some action) :
    TimeInvariant (step input state action) := by
  cases action with
  | arrival occurrence =>
      have hunseen := (nextAction_arrival haction).1
      have hchron := htime.unseen_chronological
      rw [hunseen, List.pairwise_cons] at hchron
      have hnow : state.now ≤ occurrence.request.arrival :=
        htime.now_before_unseen occurrence (hunseen ▸ List.mem_cons_self)
      exact ⟨htime.payments_chronological,
        fun payment hp => (htime.payments_before_now payment hp).trans hnow, hchron.2, hchron.1⟩
  | payment time page =>
      have hnow := nextPayment_now_le (nextAction_payment_selected haction)
      refine ⟨?_, ?_, htime.unseen_chronological, fun _ ho => (payment_lt_unseen htime haction ho).le⟩
      · refine List.pairwise_append.2 ⟨htime.payments_chronological, by simp, ?_⟩
        simpa using fun old hold => (htime.payments_before_now old hold).trans hnow
      · intro payment hp
        simp only [step, List.mem_append, List.mem_singleton] at hp
        rcases hp with hold | rfl
        · exact (htime.payments_before_now payment hold).trans hnow
        · exact le_rfl

theorem Reachable.timeInvariant {input : Instance Page} {state : State Page}
    (h : Reachable trigger input state) : TimeInvariant state := by
  induction h with
  | initial => exact initial_timeInvariant input
  | step _ ha ih => exact step_timeInvariant input _ _ ih ha

theorem final_payment_times_chronological (input : Instance Page) :
    (run trigger input (2 * input.requests.length) (initialState input)).payments.Pairwise
      fun earlier later => earlier.time ≤ later.time :=
  (reachable_final input).timeInvariant.payments_chronological

end

end PagingWithDelay.FIFO
