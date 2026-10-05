import Algorithm

/-! Definitions used both by the cost lemma and the competitive analysis. -/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- `M`, the number of threshold-payment actions made by FIFO with threshold `δ`. -/
def paymentCount (δ : Cost) (input : Instance Page) (_valid : input.Valid) : ℕ :=
  (run δ input (2 * input.requests.length) (initialState input)).payments.length

/-- The algorithm cost `ALG`, measured using the public schedule semantics. -/
def algorithmCost (δ : Cost) (input : Instance Page) (valid : input.Valid) : Cost :=
  (schedule δ input valid).totalCost input

/-- Exact proposition corresponding to Observation `obs:alg-cost` of the paper: each payment
costs one fetch plus the threshold `δ` of delay.  At `δ = 1` this is the
paper's `ALG = 2M`. -/
def AlgorithmCostClaim (δ : Cost) (input : Instance Page) (valid : input.Valid) : Prop :=
  algorithmCost δ input valid = (1 + δ) * (paymentCount δ input valid : Cost)

end
end PagingWithDelay.FIFO
