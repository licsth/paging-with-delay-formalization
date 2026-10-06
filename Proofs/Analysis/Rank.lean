import Mathlib.Data.List.Basic

/-!
# FIFO ranks

The standard potential for a FIFO (or LRU) cache measures how far each page is
from being evicted.  `rank queue x` is that measure: the page at the front of
the queue — the next one evicted — has rank `1`, the most recently fetched page
has rank `queue.length`, and a page outside the queue has rank `0`.

The lemmas below are the arithmetic of one FIFO replacement: appending a page
leaves the ranks of the others unchanged, and dropping the front lowers each of
them by one.  These are pure list lemmas, reusable for any FIFO-style potential
argument.
-/

namespace PagingWithDelay.Analysis

variable {α : Type*} [DecidableEq α]

/-- Distance of `x` from the eviction end of a FIFO queue; `0` if absent. -/
def rank (queue : List α) (x : α) : ℕ := if x ∈ queue then queue.idxOf x + 1 else 0

theorem rank_le_length (queue : List α) (x : α) : rank queue x ≤ queue.length := by
  unfold rank
  split
  · exact List.idxOf_lt_length_of_mem ‹_›
  · exact Nat.zero_le _

theorem one_le_rank_of_mem {queue : List α} {x : α} (h : x ∈ queue) :
    1 ≤ rank queue x := by
  simp [rank, h]

/-- The page just fetched sits at the back of the queue, at maximal rank. -/
theorem rank_append_self {queue : List α} {y : α} (h : y ∉ queue) :
    rank (queue ++ [y]) y = queue.length + 1 := by
  have hmem : y ∈ queue ++ [y] := by simp
  simp only [rank, hmem, if_pos]
  rw [List.idxOf_append_of_notMem h]
  simp

/-- Appending a page leaves the ranks of the pages already queued unchanged. -/
theorem rank_append_of_mem {queue : List α} {x y : α} (hx : x ∈ queue) :
    rank (queue ++ [y]) x = rank queue x := by
  simp [rank, hx, List.idxOf_append_of_mem hx]

/-- The front of the queue has rank `1`. -/
theorem rank_cons_self (head : α) (tail : List α) : rank (head :: tail) head = 1 := by
  simp [rank]

/-- Every other page sits one rank above its rank behind the front. -/
theorem rank_cons_of_mem {head x : α} {tail : List α} (hx : x ∈ tail) (hne : x ≠ head) :
    rank (head :: tail) x = rank tail x + 1 := by
  simp [rank, hx, List.idxOf_cons_ne _ (Ne.symm hne)]

end PagingWithDelay.Analysis
