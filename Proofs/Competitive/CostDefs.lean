import Proofs.EventLoop.Trigger

/-! Definitions used both by the cost lemma and the competitive analysis. -/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- `M`, the number of payments made by FIFO with the given trigger. -/
def paymentCount (trigger : Trigger) (input : Instance Page) : ℕ :=
  (run trigger input (2 * input.requests.length) (initialState input)).payments.length

/-- The algorithm cost `ALG`, measured using the public schedule semantics. -/
def algorithmCost (trigger : Trigger) (input : Instance Page) : Cost :=
  (schedule trigger input).totalCost input

/-- Exact proposition corresponding to Observation `obs:alg-cost` of the paper: each payment
costs one fetch plus the trigger's level `δ` of delay (`0` for deadlines).  At
`δ = 1` this is the paper's `ALG = 2M`. -/
def AlgorithmCostClaim (trigger : Trigger) (input : Instance Page) : Prop :=
  algorithmCost trigger input = (1 + trigger.level) * (paymentCount trigger input : Cost)

end
end PagingWithDelay.FIFO
