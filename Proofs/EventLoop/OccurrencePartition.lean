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

variable {Page : Type*} [DecidableEq Page] {δ : Cost}

noncomputable section

/-- If no payment can be selected, there are no pending occurrences. -/
theorem pending_eq_nil_of_nextPayment_none {state : State Page}
    (hpayment : nextPayment? δ state = none) : state.pending = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro occurrence hoccurrence
  obtain ⟨time, page, hexists⟩ := nextPayment_exists_of_pending
    (page := occurrence.request.page) ⟨occurrence, hoccurrence, rfl⟩
  rw [hpayment] at hexists
  simp at hexists

/-- A stopped event loop has neither unseen nor pending occurrences. -/
theorem unseen_eq_nil_and_pending_eq_nil_of_nextAction_none {state : State Page}
    (hstop : nextAction? δ state = none) : state.unseen = [] ∧ state.pending = [] := by
  unfold nextAction? at hstop
  cases hunseen : state.unseen with
  | nil =>
      constructor
      · rfl
      · cases hpayment : nextPayment? δ state with
        | none => exact pending_eq_nil_of_nextPayment_none hpayment
        | some payment => simp [hunseen, hpayment] at hstop
  | cons occurrence unseen =>
      exfalso
      cases hpayment : nextPayment? δ state with
      | none => simp [hunseen, hpayment] at hstop
      | some payment =>
          simp only [hunseen, hpayment] at hstop
          split at hstop <;> simp at hstop

/-- The chosen fuel suffices to remove every occurrence from the two live
work lists. -/
theorem final_unseen_eq_nil_and_pending_eq_nil (input : Instance Page) :
    let final := run δ input (2 * input.requests.length) (initialState input)
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

private theorem arrival_mem_unseen {state : State Page} {occurrence : Occurrence Page}
    (haction : nextAction? δ state = some (.arrival occurrence)) :
    occurrence ∈ state.unseen := by
  unfold nextAction? at haction
  cases hunseen : state.unseen with
  | nil => cases hpayment : nextPayment? δ state <;> simp [hunseen, hpayment] at haction
  | cons head tail =>
      cases hpayment : nextPayment? δ state with
      | none =>
          simp only [hunseen, hpayment] at haction
          injection haction with heq
          cases heq
          simp
      | some payment =>
          simp only [hunseen, hpayment] at haction
          split at haction
          · injection haction with heq
            cases heq
            simp
          · simp at haction

theorem initial_authentic (input : Instance Page) :
    Authentic input (initialState input) := by
  simp [Authentic, initialState]

theorem step_authentic (input : Instance Page) (state : State Page)
    (action : Action Page) (haction : nextAction? δ state = some action)
    (hauthentic : Authentic input state) :
    Authentic input (step input state action) := by
  cases action with
  | arrival occurrence =>
      have hoccurrence := hauthentic.1 occurrence (arrival_mem_unseen haction)
      constructor
      · intro candidate hcandidate
        exact hauthentic.1 candidate (by
          simp only [step] at hcandidate
          exact List.mem_of_mem_tail hcandidate)
      · constructor
        · intro candidate hcandidate
          simp only [step] at hcandidate
          split at hcandidate
          · exact hauthentic.2.1 candidate hcandidate
          · rcases List.mem_append.mp hcandidate with hold | hnew
            · exact hauthentic.2.1 candidate hold
            · have heq : candidate = occurrence := by simpa using hnew
              subst candidate
              exact hoccurrence
        · simpa [step] using hauthentic.2.2
  | payment time page =>
      constructor
      · simpa [step] using hauthentic.1
      · constructor
        · intro occurrence hoccurrence
          exact hauthentic.2.1 occurrence (List.mem_filter.mp hoccurrence).1
        · intro payment hpayment occurrence hoccurrence
          simp only [step, List.mem_append, List.mem_singleton] at hpayment
          rcases hpayment with hold | rfl
          · exact hauthentic.2.2 payment hold occurrence hoccurrence
          · exact hauthentic.2.1 occurrence (List.mem_filter.mp hoccurrence).1

theorem run_authentic (input : Instance Page) : ∀ fuel state,
    Authentic input state → Authentic input (run δ input fuel state) := by
  intro fuel
  induction fuel with
  | zero => exact fun _ h => h
  | succ fuel ih =>
      intro state h
      rw [run]
      cases haction : nextAction? δ state with
      | none => exact h
      | some action => exact ih _ (step_authentic input state action haction h)

theorem final_authentic (input : Instance Page) :
    Authentic input (run δ input (2 * input.requests.length) (initialState input)) :=
  run_authentic input _ _ (initial_authentic input)

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

/-- Pure finite-set partition of all original occurrences.  Authenticity of
the three runtime lists is supplied by `FIFO.History.Authentic`. -/
theorem inputIds_eq_runtime_union_dropped (input : Instance Page) (state : State Page)
    (hauthentic : ∀ id, id ∈ servedIds state ∪ outstandingIds state →
      id ∈ inputIds input) :
    inputIds input = servedIds state ∪ outstandingIds state ∪ droppedIds input state := by
  apply Finset.ext
  intro id
  simp only [Finset.mem_union, mem_droppedIds_iff]
  constructor
  · intro hin
    by_cases hs : id ∈ servedIds state
    · exact Or.inl (Or.inl hs)
    by_cases ho : id ∈ outstandingIds state
    · exact Or.inl (Or.inr ho)
    · exact Or.inr ⟨hin, hs, ho⟩
  · intro hright
    rcases hright with hrun | hd
    · exact hauthentic id (by simpa using hrun)
    · exact hd.1

theorem runtimeIds_subset_inputIds (input : Instance Page) (state : State Page)
    (hauthentic : Authentic input state) :
    servedIds state ∪ outstandingIds state ⊆ inputIds input := by
  intro id hid
  rcases Finset.mem_union.mp hid with hserved | houtstanding
  · have hexists : ∃ occurrence ∈ state.payments.flatMap Payment.served,
        occurrence.id = id := by
      simpa [servedIds] using hserved
    obtain ⟨occurrence, hoccurrence, hid⟩ := hexists
    obtain ⟨payment, hpayment, hoccurrence⟩ := List.mem_flatMap.mp hoccurrence
    have horiginal := hauthentic.2.2 payment hpayment occurrence hoccurrence
    exact List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨occurrence, horiginal, hid⟩)
  · have hexists : ∃ occurrence ∈ state.pending ++ state.unseen,
        occurrence.id = id := by
      have hm : id ∈ ((state.pending ++ state.unseen).map Occurrence.id) := by
        exact List.mem_toFinset.mp (by simpa [outstandingIds] using houtstanding)
      simpa only [List.mem_map] using hm
    obtain ⟨occurrence, hoccurrence, hid⟩ := hexists
    have horiginal : occurrence ∈ enumerate input.requests := by
      rcases List.mem_append.mp hoccurrence with hpending | hunseen
      · exact hauthentic.2.1 occurrence hpending
      · exact hauthentic.1 occurrence hunseen
    exact List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨occurrence, horiginal, hid⟩)

/-- At termination the runtime part of the partition is exactly the flattened
payment log. -/
theorem final_outstandingIds_eq_empty (input : Instance Page) :
    outstandingIds (run δ input (2 * input.requests.length) (initialState input)) = ∅ := by
  obtain ⟨hu, hp⟩ := final_unseen_eq_nil_and_pending_eq_nil (δ := δ) input
  simp [outstandingIds, hu, hp]

theorem final_inputIds_eq_served_union_dropped (input : Instance Page) :
    let final := run δ input (2 * input.requests.length) (initialState input)
    inputIds input = servedIds final ∪ droppedIds input final := by
  let final := run δ input (2 * input.requests.length) (initialState input)
  have hpartition := inputIds_eq_runtime_union_dropped input final
    (runtimeIds_subset_inputIds input final (final_authentic input))
  rw [final_outstandingIds_eq_empty input] at hpartition
  simpa [final] using hpartition

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
