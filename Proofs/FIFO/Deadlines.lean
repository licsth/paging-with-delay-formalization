import Algorithm
import Proofs.Competitive.AlgorithmCost

/-!
# FIFO with threshold `0` is a deadline algorithm

With threshold `0`, FIFO pays for a request as soon as it arrives, so it serves
every request before any delay accrues and meets every deadline.  This shows in
particular that online deadline algorithms exist, so the deadline lower bound
is not vacuous.
-/

namespace PagingWithDelay

noncomputable section

variable {Page : Type*} [DecidableEq Page]

namespace FIFO

/-- With threshold `0` FIFO serves every request on arrival, so it meets every
deadline: the cost identity `ALG = (1+0)·M` leaves no room for delay. -/
theorem schedule_zero_meetsDeadlines (input : Instance Page) :
    ∀ request ∈ input.requests, (schedule 0 input).requestCost request = 0 := by
  have hcost := algorithmCostClaim (0 : Cost) input
  unfold AlgorithmCostClaim algorithmCost at hcost
  rw [Schedule.totalCost, fetchCount_eq_paymentCount, add_zero, one_mul] at hcost
  have hdelay : (schedule 0 input).totalDelay input = 0 := by simpa using hcost
  intro request hrequest
  exact List.sum_eq_zero_iff.mp hdelay _ (List.mem_map_of_mem hrequest)

/-- FIFO with threshold `0` as a deadline algorithm. -/
def deadlineAlgorithm : DeadlineAlgorithm Page where
  toAlgorithm := algorithm fun _ => 0
  meetsDeadlines := schedule_zero_meetsDeadlines

end FIFO

end

end PagingWithDelay
