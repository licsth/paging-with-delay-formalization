import PagingWithDelay.Competitive.ClassCData

namespace PagingWithDelay.Competitive
open Set
variable {Page : Type*} [DecidableEq Page]
noncomputable section
structure ClassCTickWitness (input : Instance Page) (comparator : Schedule Page)
    (i : PaymentIndex input) where
  previous : PaymentIndex input
  eviction : PaymentIndex input
  interval : ResidencyInterval (Page := Page)
  previous_spec : previousIndex? input i = some previous
  eviction_ge : (previous : ℕ) + input.cacheSize ≤ (eviction : ℕ)
  interval_mem : interval ∈ residencies comparator
  interval_page : interval.page = (payment input i).page
  starts_before : interval.start ≤ paymentTime input previous
  finishes_after : interval.finish.elim True (paymentTime input eviction < ·)

private theorem witness_exists (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page) (i : PaymentIndex input)
    (h : paymentClass input comparator i = .C) :
    Nonempty (ClassCTickWitness input comparator i) := by
  obtain ⟨p, e, interval, hp, _, hge, hm, hpage, hs, hf⟩ :=
    classC_index_residency_data input valid comparator i h
  exact ⟨⟨p, e, interval, hp, hge, hm, hpage, hs, hf⟩⟩

private def witness (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page) (i : PaymentIndex input)
    (h : paymentClass input comparator i = .C) : ClassCTickWitness input comparator i :=
  Classical.choice (witness_exists input valid comparator i h)

private def endIndex (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page) (i : PaymentIndex input)
    (h : paymentClass input comparator i = .C) : PaymentIndex input :=
  let w := witness input valid comparator i h
  ⟨(w.previous : ℕ) + input.cacheSize, w.eviction_ge.trans_lt w.eviction.isLt⟩

private def assignment (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page) (i : PaymentIndex input) :
    Finset (Σ _ : PaymentIndex input, Page) :=
  if h : paymentClass input comparator i = .C then
    let w := witness input valid comparator i h
    thetaTicks input (payment input i).page w.previous
      (endIndex input valid comparator i h)
  else ∅

private theorem assignment_card (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page) (i : PaymentIndex input)
    (h : paymentClass input comparator i = .C) :
    (assignment input valid comparator i).card = input.cacheSize + 1 := by
  simp only [assignment, dif_pos h, thetaTicks_card]
  change ((witness input valid comparator i h).previous : ℕ) +
      input.cacheSize + 1 -
      ((witness input valid comparator i h).previous : ℕ) =
    input.cacheSize + 1
  omega

private theorem assignment_subset (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page) (feasible : comparator.Feasible input)
    (i : PaymentIndex input) (h : paymentClass input comparator i = .C) :
    assignment input valid comparator i ⊆ comparatorTicks input comparator := by
  intro tick htick
  simp only [assignment, dif_pos h, thetaTicks, Finset.mem_image] at htick
  obtain ⟨j, hj, rfl⟩ := htick
  let w := witness input valid comparator i h
  let e := endIndex input valid comparator i h
  rw [mem_comparatorTicks, ← w.interval_page]
  apply mem_comparatorCacheAt_paymentTime_of_residency input comparator feasible j
    w.interval w.interval_mem
  constructor
  · exact w.starts_before.trans
      (paymentTime_mono input valid (Finset.mem_Icc.mp hj).1)
  · cases hf : w.interval.finish with
    | none =>
        change True
        trivial
    | some finish =>
        have hfinish := w.finishes_after
        rw [hf] at hfinish
        change paymentTime input w.eviction < finish at hfinish
        change paymentTime input j < finish
        have hje : j ≤ e := (Finset.mem_Icc.mp hj).2
        have hew : e ≤ w.eviction := Fin.le_iff_val_le_val.mpr w.eviction_ge
        exact (paymentTime_mono input valid (hje.trans hew)).trans_lt hfinish

private theorem assignments_disjoint (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page) {i j : PaymentIndex input}
    (hi : paymentClass input comparator i = .C)
    (hj : paymentClass input comparator j = .C) (hne : i ≠ j) :
    Disjoint (assignment input valid comparator i)
      (assignment input valid comparator j) := by
  rw [Finset.disjoint_left]
  intro tick hti htj
  simp only [assignment, dif_pos hi, thetaTicks, Finset.mem_image] at hti
  simp only [assignment, dif_pos hj, thetaTicks, Finset.mem_image] at htj
  obtain ⟨indexI, hindexI, heqI⟩ := hti
  obtain ⟨indexJ, hindexJ, heqJ⟩ := htj
  have hpages : (payment input i).page = (payment input j).page :=
    congrArg Sigma.snd (heqI.trans heqJ.symm)
  let wi := witness input valid comparator i hi
  let wj := witness input valid comparator j hj
  have hd := predecessor_paymentIndexRanges_disjoint input valid hne hpages
    wi.previous_spec wj.previous_spec
  rw [Set.disjoint_left] at hd
  have hindex : (indexI : ℕ) = indexJ :=
    congrArg (fun x => ((Sigma.fst x : PaymentIndex input) : ℕ))
      (heqI.trans heqJ.symm)
  have hmemI : (indexI : ℕ) ∈
      Icc (wi.previous : ℕ) ((wi.previous : ℕ) + input.cacheSize) :=
    ⟨(Finset.mem_Icc.mp hindexI).1, (Finset.mem_Icc.mp hindexI).2⟩
  have hmemJ : (indexI : ℕ) ∈
      Icc (wj.previous : ℕ) ((wj.previous : ℕ) + input.cacheSize) := by
    rw [hindex]
    exact ⟨(Finset.mem_Icc.mp hindexJ).1, (Finset.mem_Icc.mp hindexJ).2⟩
  exact hd hmemI hmemJ

theorem classC_bound (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page) (feasible : comparator.Feasible input) :
    (input.cacheSize + 1) * classCount .C input comparator ≤
      input.cacheSize * (fifoRun input).payments.length := by
  have hassign : (input.cacheSize + 1) *
      (classIndices .C input comparator).card ≤
      (comparatorTicks input comparator).card := by
    apply mul_card_le_card_of_disjoint_assignment
      (classIndices .C input comparator) (comparatorTicks input comparator)
      (assignment input valid comparator) (input.cacheSize + 1)
    · intro i hi
      rw [assignment_card input valid comparator i (Finset.mem_filter.mp hi).2]
    · intro i hi
      exact assignment_subset input valid comparator feasible i
        (Finset.mem_filter.mp hi).2
    · intro i hi j hj hne
      exact assignments_disjoint input valid comparator
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 hne
  exact hassign.trans (comparatorTicks_card_le_of_feasible input comparator feasible)

end
end PagingWithDelay.Competitive
