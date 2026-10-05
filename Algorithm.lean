import EventLoop
import Proofs.FIFO.Feasible

/-!
# Threshold FIFO as an algorithm

Turns the event loop of `EventLoop.lean` into an `Algorithm` whose threshold may depend on the cache size.
Feasibility is proved in `Proofs/FIFO/Feasible.lean`, onlineness and nonclairvoyance in `Proofs/FIFO/Online.lean` and `Proofs/FIFO/Nonclairvoyant.lean`.
-/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- **FIFO with threshold `threshold k`** on instances with cache size `k`. -/
def algorithm (threshold : ℕ → Cost) : Algorithm Page where
  run input := schedule (threshold input.cacheSize) input
  feasible input := schedule_feasible _ input

end

end PagingWithDelay.FIFO
