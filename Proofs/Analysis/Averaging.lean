import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Averaging offline strategies

These lemmas concern only nonnegative costs, independently of paging or the
representation of an input or a schedule. A bound on the sum of the costs of
`n` offline strategies refutes a competitive claim, with an arbitrary additive
constant, for one of them.
-/

namespace PagingWithDelay.Analysis

open scoped BigOperators NNReal

/-- A strict aggregate inequality refutes a competitive claim for at least
one strategy. No division or positivity assumption on the claimed ratio is
needed, so this also handles ratio zero. -/
theorem exists_cost_lt_of_sum_lt {ι : Type*} (s : Finset ι)
    (cost : ι → ℝ≥0) (algorithm ratio additive : ℝ≥0)
    (h : ratio * (∑ i ∈ s, cost i) + s.card * additive < s.card * algorithm) :
    ∃ i ∈ s, ratio * cost i + additive < algorithm := by
  apply Finset.exists_lt_of_sum_lt
  simpa [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul] using h

/-- An upper bound on the aggregate offline cost suffices. `overhead` can
include initial cache filling, final service, and perturbations of timestamps. -/
theorem exists_cost_lt_of_sum_le {ι : Type*} (s : Finset ι)
    (cost : ι → ℝ≥0) (algorithm factor overhead ratio additive : ℝ≥0)
    (hsum : (∑ i ∈ s, cost i) ≤ factor * algorithm + overhead)
    (hslack : ratio * overhead + s.card * additive <
      ((s.card : ℝ≥0) - ratio * factor) * algorithm)
    (hratio : ratio * factor ≤ s.card) :
    ∃ i ∈ s, ratio * cost i + additive < algorithm := by
  apply exists_cost_lt_of_sum_lt s cost algorithm ratio additive
  calc
    ratio * (∑ i ∈ s, cost i) + s.card * additive
        ≤ ratio * (factor * algorithm + overhead) + s.card * additive := by gcongr
    _ = ratio * factor * algorithm + (ratio * overhead + s.card * additive) := by ring
    _ < ratio * factor * algorithm +
        ((s.card : ℝ≥0) - ratio * factor) * algorithm := by gcongr
    _ = s.card * algorithm := by
      rw [← add_mul, add_tsub_cancel_of_le hratio]

/-- Unbounded algorithm cost absorbs every fixed additive constant. The
construction supplies a family of comparators on an input of arbitrarily
large algorithm cost; its details are independent of this averaging step. -/
theorem lower_bound_of_unbounded_family {Input ι : Type*} (s : Finset ι)
    (algorithm : Input → ℝ≥0) (cost : Input → ι → ℝ≥0)
    (admissible : Input → Prop) (factor overhead ratio additive : ℝ≥0)
    (hratio : ratio * factor < s.card)
    (hfamily : ∀ bound : ℝ≥0, ∃ input, admissible input ∧
      bound < algorithm input ∧
      (∑ i ∈ s, cost input i) ≤ factor * algorithm input + overhead) :
    ∃ input, admissible input ∧ ∃ i ∈ s,
      ratio * cost input i + additive < algorithm input := by
  let slack : ℝ≥0 := s.card - ratio * factor
  have hslack : 0 < slack := tsub_pos_of_lt hratio
  obtain ⟨input, hinput, hlarge, hsum⟩ :=
    hfamily ((ratio * overhead + s.card * additive) / slack)
  refine ⟨input, hinput, exists_cost_lt_of_sum_le s (cost input)
    (algorithm input) factor overhead ratio additive hsum ?_ hratio.le⟩
  exact (div_lt_iff₀ hslack).mp hlarge |>.trans_eq (mul_comm _ _)

/-- Any ratio strictly below the family size tolerates a small multiplicative
loss in the aggregate comparison. -/
theorem exists_averaging_slack {ratio size : ℝ≥0} (h : ratio < size) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ratio * (1 + ε) < size := by
  let d := size - ratio
  let ε := d / (ratio + 1)
  have hd : 0 < d := tsub_pos_of_lt h
  have hden : 0 < ratio + 1 := by positivity
  have hε : 0 < ε := div_pos hd hden
  have heq : ε * (ratio + 1) = d := div_mul_cancel₀ _ hden.ne'
  have hsum : ratio + d = size := add_tsub_cancel_of_le h.le
  refine ⟨ε, hε, ?_⟩
  calc
    ratio * (1 + ε) < ratio * (1 + ε) + ε := lt_add_of_pos_right _ hε
    _ = ratio + ε * (ratio + 1) := by ring
    _ = size := by rw [heq, hsum]

/-- An aggregate comparison arbitrarily close to factor one yields the full
family-size lower bound. The startup overhead may depend on the chosen error,
but must be uniform over the inputs used to make algorithm cost grow. -/
theorem lower_bound_of_approximate_family {Input ι : Type*} (s : Finset ι)
    (algorithm : Input → ℝ≥0) (cost : Input → ι → ℝ≥0)
    (admissible : Input → Prop) (ratio additive : ℝ≥0)
    (hratio : ratio < s.card)
    (hfamily : ∀ ε : ℝ≥0, 0 < ε → ∃ overhead : ℝ≥0,
      ∀ bound : ℝ≥0, ∃ input, admissible input ∧ bound < algorithm input ∧
        (∑ i ∈ s, cost input i) ≤ (1 + ε) * algorithm input + overhead) :
    ∃ input, admissible input ∧ ∃ i ∈ s,
      ratio * cost input i + additive < algorithm input := by
  obtain ⟨ε, hε, hgap⟩ := exists_averaging_slack hratio
  obtain ⟨overhead, hfamily⟩ := hfamily ε hε
  exact lower_bound_of_unbounded_family s algorithm cost admissible
    (1 + ε) overhead ratio additive hgap hfamily

end PagingWithDelay.Analysis
