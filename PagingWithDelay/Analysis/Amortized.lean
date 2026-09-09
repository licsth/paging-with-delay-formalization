import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.NNReal.Basic

/-!
# Amortized analysis over a discrete schedule of events

Standard online-analysis machinery, stated for `ℝ≥0` costs and an
`ℕ`-indexed potential, with no reference to paging.

* `sum_Ico_increment` telescopes the increments of a monotone cost.
* `potential_argument` is the usual potential-function ("amortized cost")
  bound: if every step `i` of a range satisfies
  `1 + Φ (i+1) ≤ c * Δ i + Φ i`, then the number of steps is at most
  `c * ∑ Δ` plus the potential drop.

Both are used by the `k+1`-page competitive proof; neither knows about it.
-/

namespace PagingWithDelay.Analysis

open scoped NNReal

/-- Telescoping: the increments of a monotone cost sum to the total rise. -/
theorem sum_Ico_increment {f : ℕ → ℝ≥0} (hf : Monotone f) {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, (f (i + 1) - f i) = f b - f a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab, ih, add_comm]
      exact tsub_add_tsub_cancel (hf (Nat.le_succ b)) (hf hab)

/-- Telescoping bound: the increments of a monotone cost over a range are
bounded by its value at the right endpoint. -/
theorem sum_Ico_increment_le {f : ℕ → ℝ≥0} (hf : Monotone f) {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, (f (i + 1) - f i) ≤ f b := by
  rw [sum_Ico_increment hf hab]
  exact tsub_le_self

/-- Telescoping for a monotone `ℕ`-valued count. -/
theorem sum_Ico_increment_nat {f : ℕ → ℕ} (hf : Monotone f) {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, (f (i + 1) - f i) = f b - f a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab, ih]
      have h1 := hf hab
      have h2 := hf (show b ≤ b + 1 by omega)
      omega

/-- **Potential-function argument.**  A per-step amortized inequality
`1 + Φ (i+1) ≤ c * Δ i + Φ i` over `Finset.Ico a b` bounds the number of steps
by the scaled total cost plus the initial potential. -/
theorem potential_argument {Φ : ℕ → ℕ} {Δ : ℕ → ℝ≥0} {c : ℝ≥0} {a b : ℕ} (hab : a ≤ b)
    (hstep : ∀ i, a ≤ i → i < b →
      (1 : ℝ≥0) + (Φ (i + 1) : ℝ≥0) ≤ c * Δ i + (Φ i : ℝ≥0)) :
    ((b - a : ℕ) : ℝ≥0) + (Φ b : ℝ≥0) ≤ c * (∑ i ∈ Finset.Ico a b, Δ i) + (Φ a : ℝ≥0) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      have hstep' : ∀ i, a ≤ i → i < b →
          (1 : ℝ≥0) + (Φ (i + 1) : ℝ≥0) ≤ c * Δ i + (Φ i : ℝ≥0) :=
        fun i hi hib => hstep i hi (hib.trans (Nat.lt_succ_self b))
      have hlast := hstep b hab (Nat.lt_succ_self b)
      have hcount : ((b + 1 - a : ℕ) : ℝ≥0) = ((b - a : ℕ) : ℝ≥0) + 1 := by
        have : b + 1 - a = (b - a) + 1 := by omega
        rw [this]; push_cast; ring
      calc ((b + 1 - a : ℕ) : ℝ≥0) + (Φ (b + 1) : ℝ≥0)
          = ((b - a : ℕ) : ℝ≥0) + (1 + (Φ (b + 1) : ℝ≥0)) := by rw [hcount]; ring
        _ ≤ ((b - a : ℕ) : ℝ≥0) + (c * Δ b + (Φ b : ℝ≥0)) :=
              add_le_add_right hlast _
        _ = (((b - a : ℕ) : ℝ≥0) + (Φ b : ℝ≥0)) + c * Δ b := by ring
        _ ≤ (c * (∑ i ∈ Finset.Ico a b, Δ i) + (Φ a : ℝ≥0)) + c * Δ b :=
              add_le_add_left (ih hstep') _
        _ = c * (∑ i ∈ Finset.Ico a (b + 1), Δ i) + (Φ a : ℝ≥0) := by
              rw [Finset.sum_Ico_succ_top hab]; ring

end PagingWithDelay.Analysis
