import Proofs.Competitive.AlgorithmCost

/-!
# Deadline-triggered FIFO meets every deadline

Deadline-triggered FIFO pays for a page when one of its pending requests
reaches its deadline, the last moment its delay is still zero.  The cost
identity `ALG = (1+0)·M` then leaves no room for delay: every request is
served before any delay accrues.  `Algorithm.lean` packages this as
`FIFO.deadlineAlgorithm`.
-/

namespace PagingWithDelay

noncomputable section

variable {Page : Type*} [DecidableEq Page]

namespace FIFO

/-- Deadline-triggered FIFO meets every deadline: the cost identity
`ALG = (1+0)·M` leaves no room for delay. -/
theorem schedule_deadline_meetsDeadlines (input : Instance Page) :
    ∀ request ∈ input.requests, (schedule .deadline input).requestCost request = 0 := by
  have hcost := algorithmCostClaim .deadline input
  unfold AlgorithmCostClaim algorithmCost at hcost
  rw [Schedule.totalCost, fetchCount_eq_paymentCount, Trigger.level_deadline, add_zero,
    one_mul] at hcost
  have hdelay : (schedule .deadline input).totalDelay input = 0 := by simpa using hcost
  intro request hrequest
  exact List.sum_eq_zero_iff.mp hdelay _ (List.mem_map_of_mem hrequest)

end FIFO

end

end PagingWithDelay
