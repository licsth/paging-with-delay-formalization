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
      · rw [List.filter_cons_of_pos hpa, filter_eq_take_countP h.2,
          List.countP_cons_of_pos hpa, List.take_succ_cons]
      · have hnil : l.filter p = [] := by
          rw [List.filter_eq_nil_iff]
          intro b hb hpb
          exact hpa (h.1 b hb hpb)
        have hzero : l.countP p = 0 := by
          rw [List.countP_eq_length_filter, hnil]
          rfl
        rw [List.filter_cons_of_neg (by simpa using hpa),
          List.countP_cons_of_neg (by simpa using hpa), hzero, hnil, List.take_zero]

/-- Passing the test is exactly being inside the initial segment. -/
theorem lt_countP_iff :
    ∀ {l : List α}, l.Pairwise (fun x y => p y = true → p x = true) →
      ∀ (n : ℕ) (hn : n < l.length), (p l[n] = true ↔ n < l.countP p)
  | [], _, _, hn => by simp at hn
  | a :: l, h, 0, _ => by
      rw [List.pairwise_cons] at h
      by_cases hpa : p a = true
      · simp [hpa, List.countP_cons_of_pos hpa]
      · have hzero : l.countP p = 0 := by
          rw [List.countP_eq_zero]
          intro b hb hpb
          exact hpa (h.1 b hb hpb)
        simp [hpa, List.countP_cons_of_neg (by simpa using hpa), hzero]
  | a :: l, h, n + 1, hn => by
      rw [List.pairwise_cons] at h
      have hn' : n < l.length := by simpa using hn
      by_cases hpa : p a = true
      · rw [List.countP_cons_of_pos hpa]
        simpa using lt_countP_iff h.2 n hn'
      · have hzero : l.countP p = 0 := by
          rw [List.countP_eq_zero]
          intro b hb hpb
          exact hpa (h.1 b hb hpb)
        have hfalse : p l[n] ≠ true := by
          intro hcontra
          exact hpa (h.1 _ (List.getElem_mem hn') hcontra)
        simp [List.countP_cons_of_neg (by simpa using hpa), hzero, hfalse]

theorem countP_le_length (l : List α) : l.countP p ≤ l.length :=
  List.countP_le_length

/-- Folding "keep the last element passing the test" is the same as folding
over the filtered list. -/
theorem foldl_ite_eq_foldl_filter {β : Type*} (q : α → Prop) [DecidablePred q] (g : α → β) :
    ∀ (l : List α) (init : β),
      l.foldl (fun current a => if q a then g a else current) init =
        (l.filter fun a => decide (q a)).foldl (fun _ a => g a) init
  | [], _ => rfl
  | a :: l, init => by
      by_cases hq : q a
      · simp [hq, foldl_ite_eq_foldl_filter q g l]
      · simp [hq, foldl_ite_eq_foldl_filter q g l]

end PagingWithDelay.Analysis
