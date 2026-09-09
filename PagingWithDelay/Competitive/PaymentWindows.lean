import PagingWithDelay.Competitive.FIFOEviction
import PagingWithDelay.EventLoop.History

/-! FIFO-side facts about payment batches used by the class-D argument. -/

namespace PagingWithDelay.Competitive

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- Every final FIFO payment batch has aggregate delay exactly one.  This is
the threshold theorem, not an accounting assumption. -/
theorem paymentBatch_delayCost_eq_one (input : Instance Page)
    (i : PaymentIndex input) :
    (payment input i).delayCost = 1 := by
  exact FIFO.final_thresholdPayments input (payment input i)
    (List.getElem_mem (l := (fifoRun input).payments) (n := (i : ℕ)) i.isLt)

/-- Expanded form of `paymentBatch_delayCost_eq_one`, convenient for sums in
the charging proof. -/
theorem paymentBatch_sum_eq_one (input : Instance Page)
    (i : PaymentIndex input) :
    ((payment input i).served.map fun occurrence =>
      occurrence.request.delay
        (paymentTime input i - occurrence.request.arrival)).sum = 1 := by
  exact paymentBatch_delayCost_eq_one input i

/-- A request served by payment `i` arrived strictly after the canonical
FIFO eviction time of every preceding same-page payment. -/
theorem servedOccurrence_after_previous_fifo_eviction (input : Instance Page)
    (valid : input.Valid) (i : PaymentIndex input) {occurrence : Occurrence Page}
    (hserved : occurrence ∈ (payment input i).served) {previous : ℕ}
    (hprevious : previousIndex? input i = some previous) :
    ((fifoRun input).payments[previous + input.cacheSize]?).any
      (fun p => p.time < occurrence.request.arrival) := by
  have hmember : previous ∈ previousCandidates input i := by
    unfold previousIndex? at hprevious
    split at hprevious
    · rename_i hn
      injection hprevious with heq
      subst previous
      exact Finset.max'_mem _ hn
    · simp at hprevious
  have hpLt : previous < (i : ℕ) :=
    Finset.mem_range.mp (Finset.mem_filter.mp hmember).1
  have hsame : (fifoRun input).payments[previous].page = (payment input i).page := by
    have hpLen : previous < (fifoRun input).payments.length := hpLt.trans i.isLt
    have hm := (Finset.mem_filter.mp hmember).2
    rw [List.getElem?_eq_getElem hpLen] at hm
    simpa [payment] using hm
  exact (FIFO.History.final_validBatchLowerBounds input valid) i i.isLt occurrence hserved
    previous hpLt hsame |>.2


theorem servedOccurrence_page_and_arrival (input : Instance Page)
    (valid : input.Valid) (i : PaymentIndex input) {occurrence : Occurrence Page}
    (hserved : occurrence ∈ (payment input i).served) :
    occurrence.request.page = (payment input i).page ∧
      occurrence.request.arrival ≤ paymentTime input i := by
  exact FIFO.History.final_validBatches input valid (payment input i)
    (List.getElem_mem (l := (fifoRun input).payments) (n := (i : ℕ)) i.isLt)
    occurrence hserved

/-- Every occurrence paid for in batch `i` arrived in the paper's payment
window `W_i`. -/
theorem servedOccurrence_mem_paymentWindow (input : Instance Page)
    (valid : input.Valid) (i : PaymentIndex input) {occurrence : Occurrence Page}
    (hserved : occurrence ∈ (payment input i).served) :
    occurrence.request.arrival ∈ paymentWindow input i := by
  have hupper := (servedOccurrence_page_and_arrival input valid i hserved).2
  cases hp : previousIndex? input i with
  | none =>
      simpa [paymentWindow, hp] using
        (show occurrence.request.arrival ∈ Set.Icc (0 : Time) (paymentTime input i) from
          ⟨bot_le, hupper⟩)
  | some previous =>
      have hei := evictionIndex_eq_previous_add_cacheSize input valid i hp
      have hlen := previous_add_cacheSize_lt input valid i hp |>.trans i.isLt
      have het : evictionTime? input i =
          some ((fifoRun input).payments[previous + input.cacheSize]'hlen).time := by
        simp [evictionTime?, hei, List.getElem?_eq_getElem hlen]
      have hlower := servedOccurrence_after_previous_fifo_eviction
        input valid i hserved hp
      rw [List.getElem?_eq_getElem hlen] at hlower
      simpa [paymentWindow, hp, het] using
        (show occurrence.request.arrival ∈
            Set.Ioc ((fifoRun input).payments[previous + input.cacheSize]'hlen).time
              (paymentTime input i) from ⟨by simpa using hlower, hupper⟩)

theorem servedOccurrence_authentic (input : Instance Page)
    (i : PaymentIndex input) {occurrence : Occurrence Page}
    (hserved : occurrence ∈ (payment input i).served) :
    occurrence ∈ enumerate input.requests := by
  exact FIFO.History.final_authentic input |>.2.2 (payment input i)
    (List.getElem_mem (l := (fifoRun input).payments) (n := (i : ℕ)) i.isLt)
    occurrence hserved

/-- Stable occurrence identifiers never occur in two FIFO payment batches
(and are not duplicated within one batch). -/
theorem servedBatchIds_nodup (input : Instance Page) :
    (((fifoRun input).payments.flatMap FIFO.Payment.served).map Occurrence.id).Nodup := by
  simpa [fifoRun] using FIFO.History.final_servedIds_nodup (δ := 1) input

theorem servedBatches_id_disjoint (input : Instance Page)
    {i j : PaymentIndex input} (hij : (i : ℕ) < j) :
    List.Disjoint ((payment input i).served.map Occurrence.id)
      ((payment input j).served.map Occurrence.id) := by
  have hn : ((fifoRun input).payments.flatMap fun payment =>
      payment.served.map Occurrence.id).Nodup := by
    have heq : ∀ ps : List (FIFO.Payment Page),
        (ps.flatMap FIFO.Payment.served).map Occurrence.id =
          ps.flatMap (fun payment => payment.served.map Occurrence.id) := by
      intro ps
      induction ps with
      | nil => rfl
      | cons p ps ih => simp [ih]
    rw [← heq]
    exact servedBatchIds_nodup input
  have hp := (List.nodup_flatMap.mp hn).2
  exact List.pairwise_iff_get.mp hp i j hij


end
end PagingWithDelay.Competitive
