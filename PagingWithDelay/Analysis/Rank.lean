import Mathlib.Data.List.Basic

/-!
# FIFO ranks

The standard potential for a FIFO (or LRU) cache measures how far each page is
from being evicted.  `rank queue x` is that measure: the page at the front of
the queue — the next one evicted — has rank `1`, the most recently fetched page
has rank `queue.length`, and a page outside the queue has rank `0`.

`rank_shift` is the arithmetic of one FIFO replacement: every surviving page
loses exactly one rank.  These are pure list lemmas, reusable for any
FIFO-style potential argument.
-/

namespace PagingWithDelay.Analysis

variable {α : Type*} [DecidableEq α]

/-- Distance of `x` from the eviction end of a FIFO queue; `0` if absent. -/
def rank (queue : List α) (x : α) : ℕ := if x ∈ queue then queue.idxOf x + 1 else 0

theorem rank_le_length (queue : List α) (x : α) : rank queue x ≤ queue.length := by
  unfold rank
  split
  · rename_i hmem
    exact List.idxOf_lt_length_of_mem hmem
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

/-- One FIFO replacement lowers the rank of every surviving page by one. -/
theorem rank_shift {queue : List α} (hnodup : queue.Nodup) {x y : α}
    (hx : x ∈ queue) (hxy : x ≠ y) :
    rank (queue.tail ++ [y]) x + 1 = rank queue x := by
  cases queue with
  | nil => simp at hx
  | cons head tail =>
      rw [List.nodup_cons] at hnodup
      by_cases hhead : x = head
      · subst x
        have hnot : head ∉ tail ++ [y] := by
          simp only [List.mem_append, List.mem_singleton]
          rintro (h | h)
          · exact hnodup.1 h
          · exact hxy h
        simp [rank, hnot, List.idxOf_cons_self]
      · have hmem : x ∈ tail := by
          rcases List.mem_cons.mp hx with h | h
          · exact absurd h hhead
          · exact h
        have hmem' : x ∈ tail ++ [y] := by simp [hmem]
        simp only [rank, hmem', if_pos, List.tail_cons]
        rw [List.idxOf_append_of_mem hmem, List.idxOf_cons_ne _ (Ne.symm hhead)]
        simp [hx]

end PagingWithDelay.Analysis
