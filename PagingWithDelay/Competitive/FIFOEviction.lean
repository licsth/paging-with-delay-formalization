import PagingWithDelay.EventLoop.FreshQueue
import PagingWithDelay.Competitive.Core

/-!
# Eviction indices

The payment-index consequences of FIFO eviction: a repeated payment's
predecessor is at least `k` positions back, its eviction happens at index
`previous + k`, and the index ranges attached to distinct same-page payments
are disjoint.
-/

namespace PagingWithDelay.Competitive

open Set

/-- Once same-page payments are known to be more than `k` positions apart,
the corresponding closed index ranges used by the class-C charge are
disjoint.  This arithmetic endpoint lemma is independent of the trace. -/
theorem paymentIndexRanges_disjoint {k p q : ℕ} (h : p + k < q) :
    Disjoint (Icc p (p + k)) (Icc q (q + k)) := by
  rw [Set.disjoint_left]
  intro index hp hq
  exact (not_lt_of_ge hq.1) (hp.2.trans_lt h)

variable {Page : Type*} [DecidableEq Page]

/-- A preceding same-page payment's eviction index `previous+k` exists and is
strictly before the current repeated payment. -/
theorem previous_add_cacheSize_lt (input : Instance Page) (valid : input.Valid)
    (i : PaymentIndex input) {previous : ℕ}
    (hprevious : previousIndex? input i = some previous) :
    previous + input.cacheSize < (i : ℕ) := by
  have hmember : previous ∈ previousCandidates input i := by
    unfold previousIndex? at hprevious
    split at hprevious
    · rename_i hnonempty
      injection hprevious with heq
      subst previous
      exact Finset.max'_mem _ hnonempty
    · simp at hprevious
  have hlt : previous < (i : ℕ) :=
    Finset.mem_range.mp (Finset.mem_filter.mp hmember).1
  have hplen : previous < (fifoRun input).payments.length := hlt.trans i.isLt
  have hsame : (fifoRun input).payments[previous].page = (payment input i).page := by
    have hany := (Finset.mem_filter.mp hmember).2
    rw [List.getElem?_eq_getElem hplen] at hany
    simpa [payment] using hany
  exact FIFO.samePage_spacing input valid hplen i.isLt hlt hsame

/-- The predecessor-based index ranges used by two distinct same-page class-C
payments are disjoint. -/
theorem predecessor_paymentIndexRanges_disjoint (input : Instance Page)
    (valid : input.Valid) {i j : PaymentIndex input} (hne : i ≠ j)
    (hpage : (payment input i).page = (payment input j).page)
    {previousI previousJ : ℕ}
    (hpreviousI : previousIndex? input i = some previousI)
    (hpreviousJ : previousIndex? input j = some previousJ) :
    Disjoint (Icc previousI (previousI + input.cacheSize))
      (Icc previousJ (previousJ + input.cacheSize)) := by
  wlog hij : (i : ℕ) < j generalizing i j previousI previousJ
  · have hji : (j : ℕ) < i := by
      have : (i : ℕ) ≠ j := by intro h; apply hne; exact Fin.ext h
      omega
    exact (this (i := j) (j := i) (previousI := previousJ)
      (previousJ := previousI) (Ne.symm hne) hpage.symm
      hpreviousJ hpreviousI hji).symm
  have hicandidate : (i : ℕ) ∈ previousCandidates input j := by
    simp only [previousCandidates, Finset.mem_filter, Finset.mem_range]
    refine ⟨hij, ?_⟩
    rw [List.getElem?_eq_getElem i.isLt]
    simpa [payment] using hpage
  have hi_le_previousJ : (i : ℕ) ≤ previousJ := by
    unfold previousIndex? at hpreviousJ
    split at hpreviousJ
    · rename_i hnonempty
      injection hpreviousJ with heq
      subst previousJ
      exact Finset.le_max' _ _ hicandidate
    · simp at hpreviousJ
  apply paymentIndexRanges_disjoint
  exact (previous_add_cacheSize_lt input valid i hpreviousI).trans_le hi_le_previousJ

/-- Any index selected by `evictionIndex?` is no earlier than the FIFO index
`previous+k`. -/
theorem evictionIndex_ge_previous_add_cacheSize (input : Instance Page)
    (valid : input.Valid) (i : PaymentIndex input) {previous eviction : ℕ}
    (hprevious : previousIndex? input i = some previous)
    (heviction : evictionIndex? input i = some eviction) :
    previous + input.cacheSize ≤ eviction := by
  have hpredProp : previous < eviction ∧
      (((fifoRun input).payments[eviction]?).any fun event =>
        decide ((payment input i).page ∉ event.queueAfter)) = true := by
    unfold evictionIndex? at heviction
    rw [hprevious] at heviction
    simp only at heviction
    exact of_decide_eq_true (List.find?_eq_some_iff_getElem.mp heviction).1
  have hpred : previous < eviction := hpredProp.1
  have hevLen : eviction < (fifoRun input).payments.length := by
    have : eviction ∈ List.range (i : ℕ) := by
      unfold evictionIndex? at heviction
      rw [hprevious] at heviction
      exact List.mem_of_find?_eq_some heviction
    exact (List.mem_range.mp this).trans i.isLt
  by_contra hnot
  have hnear : eviction + 1 ≤ previous + input.cacheSize := by omega
  have hpLen : previous < (fifoRun input).payments.length := hpred.trans hevLen
  have hmember : previous ∈ previousCandidates input i := by
    unfold previousIndex? at hprevious
    split at hprevious
    · rename_i hn
      injection hprevious with heq
      subst previous
      exact Finset.max'_mem _ hn
    · simp at hprevious
  have hsame : (fifoRun input).payments[previous].page = (payment input i).page := by
    have hany := (Finset.mem_filter.mp hmember).2
    rw [List.getElem?_eq_getElem hpLen] at hany
    simpa [payment] using hany
  have hqueue := (FIFO.final_freshPayments input valid).queueAfter_at eviction hevLen
  change (fifoRun input).payments[eviction].queueAfter =
    FIFO.recentPages input.cacheSize
      ((fifoRun input).payments.take (eviction + 1)) at hqueue
  have hmem : (fifoRun input).payments[previous].page ∈
      FIFO.recentPages input.cacheSize
        ((fifoRun input).payments.take (eviction + 1)) :=
    FIFO.page_mem_recentPages_between valid.positiveCapacity _
      (Nat.succ_le_of_lt hevLen) (hpred.trans_le (Nat.le_succ _)) hnear
  have habsent : (payment input i).page ∉
      (fifoRun input).payments[eviction].queueAfter := by
    have hany := hpredProp.2
    rw [List.getElem?_eq_getElem hevLen] at hany
    simpa using hany
  apply habsent
  rw [hqueue, ← hsame]
  exact hmem

/-- The search-based eviction index used by the charging proof is exactly the
FIFO position `previous + k`. -/
theorem evictionIndex_eq_previous_add_cacheSize (input : Instance Page)
    (valid : input.Valid) (i : PaymentIndex input) {previous : ℕ}
    (hprevious : previousIndex? input i = some previous) :
    evictionIndex? input i = some (previous + input.cacheSize) := by
  let payments := (fifoRun input).payments
  let eviction := previous + input.cacheSize
  have heLtI : eviction < (i : ℕ) := previous_add_cacheSize_lt input valid i hprevious
  have heLen : eviction < payments.length := heLtI.trans i.isLt
  have hpMem : previous ∈ previousCandidates input i := by
    unfold previousIndex? at hprevious
    split at hprevious
    · rename_i hn
      injection hprevious with heq
      subst previous
      exact Finset.max'_mem _ hn
    · simp at hprevious
  have hpLtI : previous < (i : ℕ) :=
    Finset.mem_range.mp (Finset.mem_filter.mp hpMem).1
  have hpLen : previous < payments.length := hpLtI.trans i.isLt
  have hpPage : payments[previous].page = (payment input i).page := by
    have hm := (Finset.mem_filter.mp hpMem).2
    rw [List.getElem?_eq_getElem hpLen] at hm
    simpa [payments, payment] using hm
  have habsent : (payment input i).page ∉ payments[eviction].queueAfter := by
    have hqueue := (FIFO.final_freshPayments input valid).queueAfter_at eviction heLen
    change payments[eviction].queueAfter =
      FIFO.recentPages input.cacheSize (payments.take (eviction + 1)) at hqueue
    rw [hqueue]
    rw [show eviction + 1 = (previous + 1) + input.cacheSize by
      dsimp [eviction]; omega]
    rw [FIFO.recentPages_take_add input.cacheSize (previous + 1)
      valid.positiveCapacity payments] <;> try omega
    intro hm
    simp only [List.mem_map] at hm
    obtain ⟨p, hpIn, hpEq⟩ := hm
    obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp hpIn
    have hnLt : (n : ℕ) < input.cacheSize := by
      exact hn.trans_le (List.length_take_le _ _)
    have hjLen : previous + 1 + (n : ℕ) < payments.length := by omega
    have hpGet : p = payments[previous + 1 + (n : ℕ)] := by
      simpa [List.getElem_take, List.getElem_drop] using hget.symm
    have hjLtI : previous + 1 + (n : ℕ) < (i : ℕ) := by omega
    have hjCandidate : previous + 1 + (n : ℕ) ∈ previousCandidates input i := by
      simp only [previousCandidates, Finset.mem_filter, Finset.mem_range]
      refine ⟨hjLtI, ?_⟩
      rw [List.getElem?_eq_getElem hjLen]
      rw [← hpGet]
      simp [hpEq]
    have hmax : previous + 1 + (n : ℕ) ≤ previous := by
      unfold previousIndex? at hprevious
      split at hprevious
      · rename_i hnempty
        injection hprevious with heq
        subst previous
        exact Finset.le_max' _ _ hjCandidate
      · simp at hprevious
    omega
  have hfound : (List.range (i : ℕ)).find? (fun j =>
      previous < j ∧ (payments[j]?).any fun event =>
        (payment input i).page ∉ event.queueAfter) = some eviction := by
    apply List.find?_eq_some_iff_getElem.mpr
    constructor
    · simp [List.getElem?_eq_getElem heLen, habsent]
      dsimp [eviction]
      exact Nat.lt_add_of_pos_right valid.positiveCapacity
    refine ⟨eviction, by simpa using heLtI, by simp, ?_⟩
    intro m hm
    by_cases hprev : previous < m
    · have hmLen : m < payments.length := hm.trans heLen
      have hqueue := (FIFO.final_freshPayments input valid).queueAfter_at m hmLen
      change payments[m].queueAfter =
        FIFO.recentPages input.cacheSize (payments.take (m + 1)) at hqueue
      have hmember : payments[previous].page ∈
          FIFO.recentPages input.cacheSize (payments.take (m + 1)) :=
        FIFO.page_mem_recentPages_between valid.positiveCapacity payments
          (Nat.succ_le_of_lt hmLen) (hprev.trans_le (Nat.le_succ _)) (by omega)
      have : (payment input i).page ∈ payments[m].queueAfter := by
        rw [hqueue, ← hpPage]
        exact hmember
      simp [List.getElem_range, List.getElem?_eq_getElem hmLen, hprev, this]
    · simp [List.getElem_range, hprev]
  unfold evictionIndex?
  rw [hprevious]
  exact hfound

end PagingWithDelay.Competitive
