import EventLoop
import Proofs.FIFO.Feasible
import Proofs.FIFO.Deadlines

/-!
# FIFO as an algorithm

Turns the event loop of `EventLoop.lean` into an `Algorithm` whose threshold may depend on the cache size, and deadline-triggered FIFO into a `DeadlineAlgorithm`.
Feasibility is proved in `Proofs/FIFO/Feasible.lean`, onlineness and nonclairvoyance in `Proofs/FIFO/Online.lean` and `Proofs/FIFO/Nonclairvoyant.lean`, and that deadline-triggered FIFO meets every deadline in `Proofs/FIFO/Deadlines.lean`.
-/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- **FIFO with threshold `threshold k`** on instances with cache size `k`. -/
def algorithm (threshold : ℕ → Cost) : Algorithm Page where
  run input := schedule (.threshold (threshold input.cacheSize)) input
  feasible input := schedule_feasible _ input

/-- **Deadline-triggered FIFO**, which fetches a page when one of its pending requests reaches its deadline. -/
def deadlineAlgorithm : DeadlineAlgorithm Page where
  run input := schedule .deadline input
  feasible input := schedule_feasible _ input
  meetsDeadlines := schedule_deadline_meetsDeadlines

end

end PagingWithDelay.FIFO
