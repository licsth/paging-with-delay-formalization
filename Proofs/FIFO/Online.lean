import Proofs.FIFO.Nonclairvoyant

/-!
# FIFO is online, for every trigger

What FIFO does up to a time `t` depends only on the requests that have arrived
by `t`.  This is a consequence of nonclairvoyance
(`Proofs/FIFO/Nonclairvoyant.lean`): an instance and its truncation at `t`
reveal the same thing by `t`, for either trigger.
-/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page] {trigger : Trigger}

noncomputable section

/-- FIFO's behaviour before time `t` is what it would have been on the request
sequence truncated at `t`. -/
theorem schedule_upTo_eq (input : Instance Page) (t : Time) :
    (schedule trigger input).upTo t = (schedule trigger (input.upTo t)).upTo t := by
  have heq := (input.upTo_idem t).symm
  cases trigger with
  | threshold δ =>
      exact schedule_upTo_eq_of_reveals (reveals_threshold δ) _ _ t rfl rfl
        (Instance.AgreeUpTo.of_upTo_eq heq).requests
  | deadline =>
      exact schedule_upTo_eq_of_reveals reveals_deadline _ _ t rfl rfl
        (Instance.DeadlineAgreeUpTo.of_upTo_eq heq).requests

/-- **FIFO is an online algorithm**, for every choice of thresholds. -/
theorem algorithm_online (threshold : ℕ → Cost) :
    Algorithm.Online (FIFO.algorithm threshold (Page := Page)) :=
  (algorithm_nonclairvoyant threshold).online

/-- **Deadline-triggered FIFO is an online algorithm.** -/
theorem deadlineAlgorithm_online :
    (FIFO.deadlineAlgorithm (Page := Page)).Online :=
  deadlineAlgorithm_nonclairvoyant.online

end
end PagingWithDelay.FIFO
