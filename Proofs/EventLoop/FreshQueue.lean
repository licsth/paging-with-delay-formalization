import Proofs.EventLoop.CacheInvariant
import Proofs.EventLoop.TemporalInvariant

/-!
# Freshness of the FIFO payment log

Every payment fetches a page that is absent from the queue it replaces.  This
is what turns the abstract replay `recentPages` into the paper's closed form:
the last `k` pages of the initial queue followed by the fetched pages.
-/


namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page] {trigger : Trigger}

/-- Every payment page is absent from the queue obtained from the preceding
payments.  This is the exact history property used by the FIFO suffix proof. -/
inductive FreshPayments (capacity : ℕ) (initial : List Page) : List (Payment Page) → Prop
  | nil : FreshPayments capacity initial []
  | snoc {payments : List (Payment Page)} (h : FreshPayments capacity initial payments)
      (payment : Payment Page)
      (fresh : payment.page ∉ recentPages capacity initial payments) :
      (coherent : payment.queueAfter = recentPages capacity initial (payments ++ [payment])) →
      FreshPayments capacity initial (payments ++ [payment])

theorem FreshPayments.fresh_at {capacity : ℕ} {initial : List Page}
    {payments : List (Payment Page)}
    (h : FreshPayments capacity initial payments) (index : ℕ)
    (hindex : index < payments.length) :
    payments[index].page ∉ recentPages capacity initial (payments.take index) := by
  induction h with
  | nil => simp at hindex
  | @snoc previous hp payment hfresh coherent ih =>
      simp only [List.length_append, List.length_singleton] at hindex
      by_cases hlt : index < previous.length
      · rw [List.getElem_append_left hlt, List.take_append_of_le_length (by omega)]
        exact ih hlt
      · have heq : index = previous.length := by omega
        subst index
        simpa using hfresh

theorem FreshPayments.queueAfter_at {capacity : ℕ} {initial : List Page}
    {payments : List (Payment Page)}
    (h : FreshPayments capacity initial payments) (index : ℕ)
    (hindex : index < payments.length) :
    payments[index].queueAfter =
      recentPages capacity initial (payments.take (index + 1)) := by
  induction h with
  | nil => simp at hindex
  | @snoc previous hp payment hfresh coherent ih =>
      simp only [List.length_append, List.length_singleton] at hindex
      by_cases hlt : index < previous.length
      · rw [List.getElem_append_left hlt, List.take_append_of_le_length]
        · exact ih hlt
        · omega
      · have heq : index = previous.length := by omega
        subst index
        rw [show previous.length + 1 = (previous ++ [payment]).length by simp,
          List.take_length]
        simpa using coherent

/-- Execution invariant combining the suffix replay with freshness of every
payment at the instant it was made. -/
structure FreshQueue (input : Instance Page) (state : State Page) : Prop where
  recent : RecentQueue input state
  fresh : FreshPayments input.cacheSize input.initialCache state.payments

theorem Reachable.freshQueue {input : Instance Page} {state : State Page}
    (h : Reachable trigger input state) : FreshQueue input state := by
  induction h with
  | initial => exact ⟨initial_recentQueue input, .nil⟩
  | @step state action hr ha ih =>
      cases action with
      | arrival occurrence =>
          exact ⟨by simpa [RecentQueue, FIFO.step] using ih.recent,
            by simpa [FIFO.step] using ih.fresh⟩
      | payment time page =>
          obtain ⟨occurrence, hpending, hpage⟩ :=
            nextPayment_pending (nextAction_payment_selected ha)
          have hrecent := recentPages_append input.cacheSize input.initialCache state.payments
            state.queue
            { time := time, page := page,
              served := state.pending.filter fun occurrence => occurrence.request.page = page,
              queueAfter := insertPage input.cacheSize state.queue page } ih.recent
          refine ⟨hrecent, ih.fresh.snoc _ ?_ hrecent⟩
          rw [← ih.recent, ← hpage]
          exact hr.cacheInvariant.pending_miss occurrence hpending

theorem final_freshPayments (input : Instance Page) :
    FreshPayments input.cacheSize input.initialCache
      (run trigger input (2 * input.requests.length) (initialState input)).payments :=
  (reachable_final input).freshQueue.fresh

omit [DecidableEq Page] in private theorem insertPage_drop_suffix
    (capacity : ℕ) (hpositive : 0 < capacity) (pages : List Page) (page : Page) :
    insertPage capacity (pages.drop (pages.length - capacity)) page =
      (pages ++ [page]).drop ((pages ++ [page]).length - capacity) := by
  unfold insertPage
  simp only [List.length_drop, List.length_append, List.length_singleton]
  split
  · simp [Nat.sub_eq_zero_of_le (by omega : pages.length + 1 ≤ capacity),
      Nat.sub_eq_zero_of_le (by omega : pages.length ≤ capacity)]
  · rw [List.tail_drop, show pages.length + 1 - capacity = pages.length - capacity + 1 by omega,
      List.drop_append_of_le_length (by omega)]

/-- Concrete FIFO replay is exactly the suffix of length at most `capacity` of
the initial queue followed by the payment pages.  This is the closed form used
by the paper's cache invariant. -/
theorem recentPages_eq_lastPaymentPages (capacity : ℕ) (hpositive : 0 < capacity)
    (initial : List Page) (hinitial : initial.length ≤ capacity)
    (payments : List (Payment Page)) :
    recentPages capacity initial payments = lastPaymentPages capacity initial payments := by
  induction payments using List.reverseRecOn with
  | nil => simp [recentPages, lastPaymentPages, Nat.sub_eq_zero_of_le hinitial]
  | append_singleton payments payment ih =>
      rw [← recentPages_append capacity initial payments
        (recentPages capacity initial payments) payment rfl, ih]
      unfold lastPaymentPages
      simp only [List.map_append, List.map_singleton, ← List.append_assoc]
      exact insertPage_drop_suffix capacity hpositive
        (initial ++ payments.map Payment.page) payment.page

/-- The closed form read at one index: the entry at position `j` of the initial
queue followed by the payment pages is still in the replayed queue as long as
fewer than `capacity` entries follow it. -/
theorem getElem_mem_recentPages {capacity j : ℕ} (hpositive : 0 < capacity)
    (initial : List Page) (hinitial : initial.length ≤ capacity)
    (payments : List (Payment Page))
    (hj : j < (initial ++ payments.map Payment.page).length)
    (hnear : initial.length + payments.length ≤ j + capacity) :
    (initial ++ payments.map Payment.page)[j] ∈ recentPages capacity initial payments := by
  rw [recentPages_eq_lastPaymentPages capacity hpositive initial hinitial]
  unfold lastPaymentPages
  simp only [List.length_append, List.length_map] at hj ⊢
  let d := initial.length + payments.length - capacity
  have hdle : d ≤ j := by dsimp [d]; omega
  have hidx : j - d < (List.drop d (initial ++ payments.map Payment.page)).length := by
    simp only [List.length_drop, List.length_append, List.length_map]
    omega
  have hm := List.getElem_mem
    (l := List.drop d (initial ++ payments.map Payment.page)) (n := j - d) hidx
  convert hm using 1
  rw [List.getElem_drop]
  congr 1
  omega

end PagingWithDelay.FIFO
