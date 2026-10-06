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
  have hweight {occurrence : Occurrence Page} (h : occurrence ∈ enumerate input.requests) :
      weight occurrence.id = (schedule trigger input).requestCost occurrence.request :=
    Competitive.Schedule.requestIdWeight_eq_requestCost_of_mem_enumerate _ input h
  -- Every request position is either served by a payment or dropped as a hit.
  have hids : OccurrencePartition.inputIds input = Finset.range input.requests.length := by
    have aux : ∀ (next : ℕ) (requests : List (Request Page)),
        (enumerateFrom next requests).map Occurrence.id = List.range' next requests.length := by
      intro next requests
      induction requests generalizing next with
      | nil => rfl
      | cons request rest ih => simp [enumerateFrom, ih, List.range'_succ]
    ext id
    simp [OccurrencePartition.inputIds, enumerate, aux]
  have hdisjoint : Disjoint (OccurrencePartition.servedIds final)
      (OccurrencePartition.droppedIds input final) :=
    Finset.disjoint_left.mpr fun _ hserved hdropped =>
      ((OccurrencePartition.mem_droppedIds_iff input final _).mp hdropped).2.1 hserved
  -- A dropped request is a cache hit and pays no delay.
  have hdropped : ∑ id ∈ OccurrencePartition.droppedIds input final, weight id = 0 := by
    refine Finset.sum_eq_zero fun id hid => ?_
    obtain ⟨hinput, hnotServed, -⟩ := (OccurrencePartition.mem_droppedIds_iff input final id).mp hid
    obtain ⟨occurrence, horiginal, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hinput)
    rw [hweight horiginal]
    exact Schedule.requestCost_eq_zero_of_mem_cacheBefore _ _
      (final_dropped_occurrence_is_hit input occurrence horiginal fun hserved =>
        hnotServed (List.mem_toFinset.mpr (List.mem_map_of_mem hserved)))
  -- The requests served by a payment pay delay `δ` in total.
  have hpayment : ∀ payment ∈ final.payments,
      (payment.served.map (weight ∘ Occurrence.id)).sum = trigger.level := by
    intro payment hpayment
    rw [← final_thresholdPayments input payment hpayment, Payment.delayCost]
    refine congrArg List.sum (List.map_congr_left fun occurrence hoccurrence => ?_)
    rw [Function.comp_apply,
      hweight ((OccurrencePartition.final_authentic input).2.2 payment hpayment occurrence hoccurrence),
      final_served_requestCost_eq input payment hpayment occurrence hoccurrence]
  have hserved : ∑ id ∈ OccurrencePartition.servedIds final, weight id =
      trigger.level * final.payments.length := by
    rw [OccurrencePartition.servedIds,
      List.sum_toFinset weight (History.final_servedIds_nodup input), List.map_map, OccurrencePartition.sum_flattened_payments, List.map_congr_left hpayment,
      List.map_const', List.sum_replicate, nsmul_eq_mul, mul_comm]
  have hdelay : (schedule trigger input).totalDelay input =
      trigger.level * final.payments.length := by
    rw [← Competitive.Schedule.sum_requestIdWeight_range, ← hids,
      OccurrencePartition.final_inputIds_eq_served_union_dropped, Finset.sum_union hdisjoint,
      hserved, hdropped, add_zero]
  rw [AlgorithmCostClaim, algorithmCost, Schedule.totalCost, fetchCount_eq_paymentCount, hdelay,
    paymentCount]
  ring

end
end PagingWithDelay.FIFO
