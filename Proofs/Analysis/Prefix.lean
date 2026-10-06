import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Count

/-!
# Chronological prefixes

A list sorted so that passing a test at a later position forces it at every
earlier one — a chronological event log tested against a deadline — splits
into a prefix of passing elements and a suffix of failing ones.

These are pure list lemmas, reusable wherever an online argument has to talk
about "the events that have happened by time `t`".
-/

namespace PagingWithDelay.Analysis

variable {α : Type*} {p : α → Bool}

/-- The elements passing a downward-closed test form an initial segment. -/
theorem filter_eq_take_countP :
    ∀ {l : List α}, l.Pairwise (fun x y => p y = true → p x = true) →
      l.filter p = l.take (l.countP p)
  | [], _ => by simp
  | a :: l, h => by
      rw [List.pairwise_cons] at h
      by_cases hpa : p a = true
      · simp [hpa, filter_eq_take_countP h.2]
      · have hnone : ∀ b ∈ l, ¬p b = true := fun b hb hpb => hpa (h.1 b hb hpb)
        simp [hpa, List.countP_eq_zero.mpr hnone, List.filter_eq_nil_iff.mpr hnone]

/-- Passing the test is exactly being inside the initial segment. -/
theorem lt_countP_iff :
    ∀ {l : List α}, l.Pairwise (fun x y => p y = true → p x = true) →
      ∀ (n : ℕ) (hn : n < l.length), (p l[n] = true ↔ n < l.countP p)
  | [], _, _, hn => by simp at hn
  | a :: l, h, n, hn => by
      rw [List.pairwise_cons] at h
      by_cases hpa : p a = true
      · cases n with
        | zero => simp [hpa]
        | succ n => simpa [hpa] using lt_countP_iff h.2 n (by simpa using hn)
      · have hnone : ∀ b ∈ l, ¬p b = true := fun b hb hpb => hpa (h.1 b hb hpb)
        cases n <;> simp [hpa, List.countP_eq_zero.mpr hnone, hnone _ (List.getElem_mem _)]

end PagingWithDelay.Analysis
