import PagingWithDelay.Competitive.ClassAB
import PagingWithDelay.Competitive.ClassC
import PagingWithDelay.Competitive.ClassD
import PagingWithDelay.Competitive.AlgorithmCost

/-!
# Final competitive-ratio arithmetic

This module combines the payment partition, the three per-class bounds, and
the proved algorithm-cost accounting lemma.
-/

namespace PagingWithDelay.Competitive

variable {Page : Type*} [DecidableEq Page]
noncomputable section

theorem paymentCount_le (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page) (feasible : comparator.Feasible input) :
    (FIFO.paymentCount 1 input valid : Cost) ≤
      (input.cacheSize + 1 : ℕ) * comparator.totalCost input := by
  let M := (fifoRun input).payments.length
  let A := classCount .A input comparator
  let B := classCount .B input comparator
  let C := classCount .C input comparator
  let D := classCount .D input comparator
  have hpartition : M = A + B + C + D := by
    exact payment_classes_exhaustive input comparator
  have hAB : A + B ≤ comparator.fetchCount :=
    classA_classB_bound input valid comparator feasible
  have hC : (input.cacheSize + 1) * C ≤ input.cacheSize * M :=
    classC_bound input valid comparator feasible
  have hNat : M ≤ (input.cacheSize + 1) * (comparator.fetchCount + D) := by
    nlinarith
  have hcast : (M : Cost) ≤
      (input.cacheSize + 1 : ℕ) *
        ((comparator.fetchCount : Cost) + (D : Cost)) := by
    exact_mod_cast hNat
  have hD : (D : Cost) ≤ comparator.totalDelay input :=
    classD_bound input valid comparator feasible
  have htotal : (comparator.fetchCount : Cost) + (D : Cost) ≤
      comparator.totalCost input := by
    unfold Schedule.totalCost
    simpa using add_le_add_left hD (comparator.fetchCount : Cost)
  change (M : Cost) ≤ _
  exact hcast.trans (mul_le_mul_of_nonneg_left htotal (by positivity))

/-- Once the independent `ALG = 2M` accounting lemma is supplied, the class
bounds imply the paper-facing competitive-ratio claim by arithmetic alone. -/
theorem competitiveRatio_of_algorithmCostClaim (input : Instance Page)
    (valid : input.Valid) (algorithmCostClaim : FIFO.AlgorithmCostClaim 1 input valid) :
    ∀ comparator : Schedule Page, comparator.Feasible input →
      (FIFO.schedule 1 input valid).totalCost input ≤
        (2 * input.cacheSize + 2 : ℕ) * comparator.totalCost input := by
  intro comparator feasible
  have hM := paymentCount_le input valid comparator feasible
  unfold FIFO.AlgorithmCostClaim FIFO.algorithmCost at algorithmCostClaim
  rw [algorithmCostClaim, show (1 + 1 : Cost) = 2 by norm_num]
  calc
    2 * (FIFO.paymentCount 1 input valid : Cost) ≤
        2 * ((input.cacheSize + 1 : ℕ) * comparator.totalCost input) :=
      mul_le_mul_right hM 2
    _ = (2 * input.cacheSize + 2 : ℕ) * comparator.totalCost input := by
      push_cast
      ring

/-- The final competitive-ratio result; no additional fact is assumed here. -/
theorem competitiveRatio (input : Instance Page) (valid : input.Valid) :
    ∀ comparator : Schedule Page, comparator.Feasible input →
      (FIFO.schedule 1 input valid).totalCost input ≤
        (2 * input.cacheSize + 2 : ℕ) * comparator.totalCost input :=
  competitiveRatio_of_algorithmCostClaim input valid
    (FIFO.algorithmCostClaim 1 input valid)

end
end PagingWithDelay.Competitive
