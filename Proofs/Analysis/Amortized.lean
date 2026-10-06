import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.NNReal.Basic

/-!
# Telescoping a monotone count

`sum_Ico_increment_nat` is used by the payment accounting of
`RankPotential/Final.lean`.
-/

namespace PagingWithDelay.Analysis

/-- Telescoping: the increments of a monotone `ℕ`-valued count sum to the total rise. -/
theorem sum_Ico_increment_nat {f : ℕ → ℕ} (hf : Monotone f) {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, (f (i + 1) - f i) = f b - f a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab, ih]
      have := hf hab
      have := hf (Nat.le_add_right b 1)
      omega

end PagingWithDelay.Analysis
