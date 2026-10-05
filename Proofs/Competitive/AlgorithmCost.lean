import Proofs.Competitive.CostDefs
import Proofs.Competitive.DelayAccounting
import Proofs.EventLoop.ServiceSemantics

/-!
# Cost of FIFO payments

This file proves Observation `obs:alg-cost` of `submission.tex`,
`ALG = (1+δ)·M`. All accounting facts are derived directly from `FIFO.run`; no
property of FIFO is introduced as an assumption here.
-/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- The fetch part of the paper's accounting argument: the public schedule is
the erasure of the payment log, with exactly one fetch event per payment. -/
theorem fetchCount_eq_paymentCount (trigger : Trigger)
    (input : Instance Page) :
    (schedule trigger input).fetchCount = paymentCount trigger input := by
  simp [Schedule.fetchCount, schedule, paymentCount]

/-- The public cost of FIFO is exactly `1 + δ` per payment, `δ` the trigger's
level: one fetch, and the `δ` units of delay the payment released. -/
theorem algorithmCostClaim (trigger : Trigger) (input : Instance Page) :
    AlgorithmCostClaim trigger input := by
  let final := run trigger input (2 * input.requests.length) (initialState input)
  let weight := Competitive.Schedule.requestIdWeight (schedule trigger input) input
  have hids : OccurrencePartition.inputIds input = Finset.range input.requests.length := by
    have aux : ∀ (next : ℕ) (requests : List (Request Page)),
        (enumerateFrom next requests |>.map Occurrence.id) =
          List.range' next requests.length := by
      intro next requests
      induction requests generalizing next with
      | nil => simp [enumerateFrom]
      | cons request rest ih => simp [enumerateFrom, ih, List.range'_succ]
    apply Finset.ext
    intro id
    simp [OccurrencePartition.inputIds, enumerate, aux]
  have hpartition : Finset.range input.requests.length =
      OccurrencePartition.servedIds final ∪
        OccurrencePartition.droppedIds input final := by
    rw [← hids]
    exact OccurrencePartition.final_inputIds_eq_served_union_dropped input
  have hdisjoint : Disjoint (OccurrencePartition.servedIds final)
      (OccurrencePartition.droppedIds input final) := by
    rw [Finset.disjoint_left]
    intro id hserved hdropped
    exact ((OccurrencePartition.mem_droppedIds_iff input final id).mp hdropped).2.1 hserved
  have hdroppedZero : ∀ id ∈ OccurrencePartition.droppedIds input final,
      weight id = 0 := by
    intro id hdropped
    have hinput : id ∈ OccurrencePartition.inputIds input :=
      ((OccurrencePartition.mem_droppedIds_iff input final id).mp hdropped).1
    change id ∈ (enumerate input.requests |>.map Occurrence.id).toFinset at hinput
    rw [List.mem_toFinset] at hinput
    obtain ⟨occurrence, horiginal, hid⟩ := List.mem_map.mp hinput
    subst id
    rw [show weight occurrence.id =
        (schedule trigger input).requestCost occurrence.request by
      exact Competitive.Schedule.requestIdWeight_eq_requestCost_of_mem_enumerate
        (schedule trigger input) input horiginal]
    apply Schedule.requestCost_eq_zero_of_mem_cacheBefore
    apply final_dropped_occurrence_is_hit input occurrence horiginal
    intro hserved
    apply ((OccurrencePartition.mem_droppedIds_iff input final occurrence.id).mp
      hdropped).2.1
    unfold OccurrencePartition.servedIds
    rw [List.mem_toFinset]
    exact List.mem_map.mpr ⟨occurrence, hserved, rfl⟩
  have hservedNodup :
      ((final.payments.flatMap Payment.served).map Occurrence.id).Nodup := by
    exact History.final_servedIds_nodup input
  have hservedSum : (∑ id ∈ OccurrencePartition.servedIds final, weight id) =
      ((final.payments.flatMap Payment.served).map fun occurrence =>
        (schedule trigger input).requestCost occurrence.request).sum := by
    unfold OccurrencePartition.servedIds
    rw [List.sum_toFinset weight hservedNodup]
    apply congrArg List.sum
    rw [List.map_map]
    apply List.map_congr_left
    intro occurrence hoccurrence
    obtain ⟨payment, hpayment, hoccurrence⟩ := List.mem_flatMap.mp hoccurrence
    have horiginal := OccurrencePartition.final_authentic input |>.2.2
      payment hpayment occurrence hoccurrence
    exact Competitive.Schedule.requestIdWeight_eq_requestCost_of_mem_enumerate
      (schedule trigger input) input horiginal
  have hpublicDelay : (schedule trigger input).totalDelay input =
      (final.payments.map Payment.delayCost).sum := by
    rw [← Competitive.Schedule.sum_requestIdWeight_range (schedule trigger input) input]
    rw [hpartition, Finset.sum_union hdisjoint]
    rw [hservedSum]
    have hz : (∑ id ∈ OccurrencePartition.droppedIds input final, weight id) = 0 := by
      exact Finset.sum_eq_zero fun id hid => hdroppedZero id hid
    rw [hz, add_zero]
    rw [OccurrencePartition.sum_flattened_payments]
    apply congrArg List.sum
    apply List.map_congr_left
    intro payment hpayment
    unfold Payment.delayCost
    apply congrArg List.sum
    apply List.map_congr_left
    intro occurrence hoccurrence
    exact final_served_requestCost_eq input payment hpayment occurrence hoccurrence
  have hthreshold : (final.payments.map Payment.delayCost).sum =
      trigger.level * (final.payments.length : Cost) := by
    calc
      (final.payments.map Payment.delayCost).sum =
          (final.payments.map fun _ => trigger.level).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro payment hpayment
            exact final_thresholdPayments input payment hpayment
      _ = trigger.level * (final.payments.length : Cost) := by
            rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
            ring
  unfold AlgorithmCostClaim algorithmCost paymentCount
  rw [Schedule.totalCost, fetchCount_eq_paymentCount trigger input]
  change (final.payments.length : Cost) + (schedule trigger input).totalDelay input =
    (1 + trigger.level) * (final.payments.length : Cost)
  rw [hpublicDelay, hthreshold]
  ring


end
end PagingWithDelay.FIFO
