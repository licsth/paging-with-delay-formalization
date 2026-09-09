import PagingWithDelay.Competitive.PaymentWindows
import PagingWithDelay.Competitive.ClassDSemantics
import PagingWithDelay.Competitive.DelayAccounting

namespace PagingWithDelay.Competitive

variable {Page : Type*} [DecidableEq Page]
noncomputable section

private def classDAssigned (input : Instance Page) (i : PaymentIndex input) :
    Finset ℕ := ((payment input i).served.map Occurrence.id).toFinset

private theorem sum_toFinset_eq {X : Type*} [DecidableEq X]
    (weight : X → Cost) (xs : List X) (hn : xs.Nodup) :
    (∑ x ∈ xs.toFinset, weight x) = (xs.map weight).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hn
      simp [hn.1, ih hn.2]

private theorem servedIds_nodup_at (input : Instance Page)
    (i : PaymentIndex input) :
    ((payment input i).served.map Occurrence.id).Nodup := by
  have hall : ((fifoRun input).payments.flatMap fun p =>
      p.served.map Occurrence.id).Nodup := by
    have heq : ∀ ps : List (FIFO.Payment Page),
        (ps.flatMap FIFO.Payment.served).map Occurrence.id =
          ps.flatMap (fun p => p.served.map Occurrence.id) := by
      intro ps
      induction ps with
      | nil => rfl
      | cons p ps ih => simp [ih]
    rw [← heq]
    exact servedBatchIds_nodup input
  exact (List.nodup_flatMap.mp hall).1 (payment input i)
    (List.getElem_mem i.isLt)

private theorem classD_occurrence_charge
    (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page) (feasible : comparator.Feasible input)
    (i : PaymentIndex input) (hclass : paymentClass input comparator i = .D)
    {occurrence : Occurrence Page}
    (hserved : occurrence ∈ (payment input i).served) :
    occurrence.request.delay
        (paymentTime input i - occurrence.request.arrival) ≤
      Schedule.requestIdWeight comparator input occurrence.id := by
  have hauth := servedOccurrence_authentic input i hserved
  have hrequest : occurrence.request ∈ input.requests := by
    rw [← FIFO.enumerate_map_request input.requests]
    exact List.mem_map_of_mem hauth
  have hp := servedOccurrence_page_and_arrival input valid i hserved
  have hwindow := servedOccurrence_mem_paymentWindow input valid i hserved
  have hD := isClassD_of_paymentClass_eq input comparator i hclass
  obtain ⟨service, hservice, htime⟩ := classD_serviceTime_ge_paymentTime
    input comparator feasible i occurrence.request hrequest hp.1 hwindow hD
  have hwait : paymentTime input i - occurrence.request.arrival ≤
      service - occurrence.request.arrival := tsub_le_tsub_right htime _
  have hdelay := occurrence.request.delay_mono hwait
  rw [Schedule.requestIdWeight_eq_requestCost_of_mem_enumerate comparator input hauth]
  unfold Schedule.requestCost Schedule.serviceDelay
  rw [hservice]
  exact hdelay

private theorem classD_batch_charge
    (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page) (feasible : comparator.Feasible input)
    (i : PaymentIndex input) (hclass : paymentClass input comparator i = .D) :
    1 ≤ ∑ id ∈ classDAssigned input i,
      Schedule.requestIdWeight comparator input id := by
  rw [← paymentBatch_sum_eq_one input i]
  unfold classDAssigned
  rw [sum_toFinset_eq _ _ (servedIds_nodup_at input i)]
  simp only [List.map_map]
  apply List.sum_le_sum
  intro occurrence hserved
  exact classD_occurrence_charge input valid comparator feasible i hclass hserved

private theorem classD_assigned_authentic (input : Instance Page)
    (i : PaymentIndex input) :
    classDAssigned input i ⊆ Finset.range input.requests.length := by
  intro id hid
  simp only [classDAssigned, List.mem_toFinset, List.mem_map] at hid
  obtain ⟨occurrence, hserved, rfl⟩ := hid
  exact Finset.mem_range.mpr (Schedule.id_lt_of_mem_enumerate
    (servedOccurrence_authentic input i hserved))

private theorem classD_assigned_disjoint (input : Instance Page)
    {i j : PaymentIndex input} (hne : i ≠ j) :
    Disjoint (classDAssigned input i) (classDAssigned input j) := by
  unfold classDAssigned
  rw [List.disjoint_toFinset_iff_disjoint]
  rcases lt_or_gt_of_ne (show (i : ℕ) ≠ j from fun h => hne (Fin.ext h)) with hij | hji
  · exact servedBatches_id_disjoint input hij
  · exact (servedBatches_id_disjoint input hji).symm

/-- Class D charges one unit to comparator delay. -/
theorem classD_bound (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page) (feasible : comparator.Feasible input) :
    (classCount .D input comparator : Cost) ≤ comparator.totalDelay input := by
  apply Schedule.card_le_totalDelay_of_disjoint_id_charges comparator input
    (classIndices .D input comparator) (classDAssigned input)
  · intro i hi
    exact classD_batch_charge input valid comparator feasible i
      (Finset.mem_filter.mp hi).2
  · intro i _
    exact classD_assigned_authentic input i
  · intro i _ j _ hne
    exact classD_assigned_disjoint input hne

end
end PagingWithDelay.Competitive
