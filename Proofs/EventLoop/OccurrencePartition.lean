import Proofs.EventLoop.TemporalInvariant

/-!
# Occurrence bookkeeping for FIFO

This file contains only consequences of the event loop.  In particular,
`droppedIds` is bookkeeping terminology for input occurrences no longer in
`unseen`, `pending`, or a payment batch; it does not assert that such an
occurrence was a cache hit.  The latter requires the separate cache-trace
bridge.
-/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page] {trigger : Trigger}

noncomputable section

/-- A stopped event loop has neither unseen nor pending occurrences. -/
theorem unseen_eq_nil_and_pending_eq_nil_of_nextAction_none {state : State Page}
    (hstop : nextAction? trigger state = none) : state.unseen = [] ∧ state.pending = [] := by
  have h : state.unseen = [] ∧ nextPayment? trigger state = none := by
    unfold nextAction? at hstop; split at hstop <;> (try split at hstop) <;> simp_all
  refine ⟨h.1, List.eq_nil_iff_forall_not_mem.mpr fun occurrence hoccurrence => ?_⟩
  obtain ⟨time, page, hexists⟩ := nextPayment_exists_of_pending (trigger := trigger)
    ⟨occurrence, hoccurrence, rfl⟩
  simp [h.2] at hexists

/-- The chosen fuel suffices to remove every occurrence from the two live
work lists. -/
theorem final_unseen_eq_nil_and_pending_eq_nil (input : Instance Page) :
    let final := run trigger input (2 * input.requests.length) (initialState input)
    final.unseen = [] ∧ final.pending = [] := by
  exact unseen_eq_nil_and_pending_eq_nil_of_nextAction_none (run_initial_finished input)

namespace OccurrencePartition

/-- All occurrences retained by the event loop are occurrences of the input.
This is an invariant proved from `step`, not an assumption on FIFO. -/
def Authentic (input : Instance Page) (state : State Page) : Prop :=
  (∀ occurrence ∈ state.unseen, occurrence ∈ enumerate input.requests) ∧
  (∀ occurrence ∈ state.pending, occurrence ∈ enumerate input.requests) ∧
  (∀ payment ∈ state.payments, ∀ occurrence ∈ payment.served,
    occurrence ∈ enumerate input.requests)

theorem initial_authentic (input : Instance Page) :
    Authentic input (initialState input) := by
  simp [Authentic, initialState]

theorem step_authentic (input : Instance Page) (state : State Page)
    (action : Action Page) (haction : nextAction? trigger state = some action)
    (hauthentic : Authentic input state) :
    Authentic input (step input state action) := by
  cases action with
  | arrival occurrence =>
      refine ⟨fun o ho => hauthentic.1 o (List.mem_of_mem_tail ho), fun o ho => ?_,
        hauthentic.2.2⟩
      simp only [step] at ho
      split at ho
      · exact hauthentic.2.1 o ho
      · rcases List.mem_append.mp ho with ho | ho
        · exact hauthentic.2.1 o ho
        · rw [List.mem_singleton.1 ho]
          exact hauthentic.1 occurrence (arrival_mem_unseen haction)
  | payment time page =>
      refine ⟨hauthentic.1, fun o ho => hauthentic.2.1 o (List.mem_filter.mp ho).1, ?_⟩
      intro payment hpayment o ho
      simp only [step, List.mem_append, List.mem_singleton] at hpayment
      rcases hpayment with hold | rfl
      · exact hauthentic.2.2 payment hold o ho
      · exact hauthentic.2.1 o (List.mem_filter.mp ho).1

theorem final_authentic (input : Instance Page) :
    Authentic input (run trigger input (2 * input.requests.length) (initialState input)) := by
  suffices ∀ {state}, Reachable trigger input state → Authentic input state from
    this (reachable_final input)
  intro state h
  induction h with
  | initial => exact initial_authentic input
  | step _ ha ih => exact step_authentic input _ _ ha ih

/-- Identifiers in the original request list. -/
def inputIds (input : Instance Page) : Finset ℕ :=
  (enumerate input.requests |>.map Occurrence.id).toFinset

/-- Identifiers already placed in a FIFO payment batch. -/
def servedIds (state : State Page) : Finset ℕ :=
  (state.payments.flatMap Payment.served |>.map Occurrence.id).toFinset

/-- Identifiers still waiting to arrive or be served. -/
def outstandingIds (state : State Page) : Finset ℕ :=
  ((state.pending ++ state.unseen).map Occurrence.id).toFinset

/-- Input identifiers absent from both the payment log and the live work
lists.  A later semantic lemma identifies precisely these with arrival hits. -/
def droppedIds (input : Instance Page) (state : State Page) : Finset ℕ :=
  inputIds input \ (servedIds state ∪ outstandingIds state)

theorem mem_droppedIds_iff (input : Instance Page) (state : State Page) (id : ℕ) :
    id ∈ droppedIds input state ↔
      id ∈ inputIds input ∧ id ∉ servedIds state ∧ id ∉ outstandingIds state := by
  simp [droppedIds]

/-- At termination the runtime part of the partition is exactly the flattened
payment log. -/
theorem final_outstandingIds_eq_empty (input : Instance Page) :
    outstandingIds (run trigger input (2 * input.requests.length) (initialState input)) = ∅ := by
  obtain ⟨hu, hp⟩ := final_unseen_eq_nil_and_pending_eq_nil (trigger := trigger) input
  simp [outstandingIds, hu, hp]

theorem final_inputIds_eq_served_union_dropped (input : Instance Page) :
    let final := run trigger input (2 * input.requests.length) (initialState input)
    inputIds input = servedIds final ∪ droppedIds input final := by
  intro final
  have hsub : servedIds final ⊆ inputIds input := by
    intro id hid
    simp only [servedIds, List.mem_toFinset, List.mem_map, List.mem_flatMap] at hid
    obtain ⟨occurrence, ⟨payment, hpayment, hoccurrence⟩, rfl⟩ := hid
    exact List.mem_toFinset.2 (List.mem_map_of_mem
      ((final_authentic input).2.2 payment hpayment occurrence hoccurrence))
  rw [droppedIds, final_outstandingIds_eq_empty, Finset.union_empty,
    Finset.union_sdiff_of_subset hsub]

/-- Mapping a function over all payment batches and then summing is the same
as summing the per-batch sums.  This is the regrouping step used in cost
accounting; it neither duplicates nor discards an occurrence. -/
theorem sum_flattened_payments (state : State Page) (weight : Occurrence Page → Cost) :
    ((state.payments.flatMap Payment.served).map weight).sum =
      (state.payments.map fun payment => (payment.served.map weight).sum).sum := by
  induction state.payments with
  | nil => rfl
  | cons payment payments ih => simp [ih]

end OccurrencePartition

end
end PagingWithDelay.FIFO
