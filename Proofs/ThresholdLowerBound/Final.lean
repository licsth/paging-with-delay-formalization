import Proofs.ThresholdLowerBound.Scale
import Proofs.ThresholdLowerBound.RoundRobin
import Proofs.Basic.Competitive

/-!
# No threshold algorithm beats `2k + 3/2`

Two adversaries, one per range of the threshold `δ`:

* `exists_input_large` (the deadline adversary, scaled) forces ratio
  `(1 + δ)(k + 1/2)`;
* `exists_input_roundRobin` forces ratio `(k + 1)(1 + 1/δ)`.

They cross at `δ = (k + 1)/(k + 1/2)`, where both equal `2k + 3/2`.  For
`δ` at least this value the first adversary wins, below it the second.
-/

namespace PagingWithDelay.ThresholdLowerBound

noncomputable section

variable {Page : Type*} [DecidableEq Page]

/-- A slope advantage beats any additive constant for large `N`. -/
private theorem exists_large {r a m p q b : Cost} (h : r * p < m * q) :
    ∃ N : ℕ, 1 ≤ N ∧ r * (p * N + b) + m * a < m * q * N := by
  have hd : 0 < m * q - r * p := tsub_pos_of_lt h
  obtain ⟨n, hn⟩ := Archimedean.arch (r * b + m * a) hd
  refine ⟨n + 1, by omega, ?_⟩
  rw [nsmul_eq_mul] at hn
  have hsplit : m * q = r * p + (m * q - r * p) := (add_tsub_cancel_of_le h.le).symm
  have hlt : r * b + m * a < (n + 1 : ℕ) * (m * q - r * p) :=
    lt_of_le_of_lt hn (by push_cast; exact mul_lt_mul_of_pos_right (lt_add_one _) hd)
  calc r * (p * ((n + 1 : ℕ) : Cost) + b) + m * a
      = r * p * ((n + 1 : ℕ) : Cost) + (r * b + m * a) := by ring
    _ < r * p * ((n + 1 : ℕ) : Cost) + ((n + 1 : ℕ) : Cost) * (m * q - r * p) :=
        add_lt_add_right hlt _
    _ = m * q * ((n + 1 : ℕ) : Cost) := by
        rw [mul_comm (r * p), ← mul_add, ← hsplit, mul_comm]

/-- Turning the two cost estimates into a violation. -/
private theorem violation {r a m p q b ALG OPT : Cost} {N : ℕ} (hm : 0 < m)
    (hN : r * (p * N + b) + m * a < m * q * N)
    (halg : q * N ≤ ALG) (hopt : m * OPT ≤ p * N + b) : r * OPT + a < ALG := by
  have : m * (r * OPT + a) < m * ALG :=
    calc m * (r * OPT + a) = r * (m * OPT) + m * a := by ring
      _ ≤ r * (p * N + b) + m * a := by gcongr
      _ < m * q * N := hN
      _ = m * (q * N) := by ring
      _ ≤ m * ALG := by gcongr
  exact lt_of_mul_lt_mul_left this hm.le

/-- **The `2k + 3/2` lower bound for threshold algorithms.** -/
theorem not_competitive {k : ℕ} (hk : 1 ≤ k) (pages : Fin (k + 2) ↪ Page)
    {algorithm : ThresholdAlgorithm Page} (online : algorithm.Online)
    {ratio : ℕ → Cost} (hratio : 2 * ratio k < 4 * k + 3) :
    ¬ algorithm.Competitive ratio := by
  apply Algorithm.not_competitive_of_schedules
  intro additive
  set δ := algorithm.threshold k with hδ
  have hδpos : 0 < δ := algorithm.threshold_pos k
  have hratioR : 2 * (ratio k : ℝ) < 4 * k + 3 := by exact_mod_cast hratio
  by_cases hlarge : (2 * k + 2 : Cost) ≤ (2 * k + 1) * δ
  · -- large threshold: the scaled deadline adversary
    have hlargeR : (2 * k + 2 : ℝ) ≤ (2 * k + 1) * δ := by exact_mod_cast hlarge
    have hslope : ratio k * 2 < (2 * k + 1) * (1 + δ) := by
      rw [← NNReal.coe_lt_coe]; push_cast; nlinarith
    obtain ⟨N, hN, hbeat⟩ := exists_large (b := 2 * k + (2 * k + 1)) (a := additive k) hslope
    obtain ⟨input, comparator, hsize, -, hfeasible, halg, hopt⟩ :=
      exists_input_large algorithm online hk pages hN
    refine ⟨input, comparator, trivial, hfeasible, ?_⟩
    rw [hsize]
    exact violation (by positivity) hbeat halg (by rw [add_assoc] at hopt; exact hopt)
  · -- small threshold: round robin on `k + 1` pages
    have hsmallR : (2 * k + 1) * (δ : ℝ) < 2 * k + 2 := by
      have := lt_of_not_ge hlarge
      exact_mod_cast this
    have hδR : (0 : ℝ) < δ := by exact_mod_cast hδpos
    have hslope : ratio k * δ < (k + 1) * (1 + δ) := by
      rw [← NNReal.coe_lt_coe]; push_cast; nlinarith
    obtain ⟨N, -, hbeat⟩ := exists_large (b := (k + 1) * (k + 2)) (a := additive k) hslope
    obtain ⟨input, comparator, hsize, -, hfeasible, halg, hopt⟩ :=
      exists_input_roundRobin algorithm online hk (Fin.castSuccEmb.trans pages) N
    refine ⟨input, comparator, trivial, hfeasible, ?_⟩
    rw [hsize]
    exact violation (by positivity) hbeat halg (by rw [mul_comm (N : Cost)] at hopt; exact hopt)

end
end PagingWithDelay.ThresholdLowerBound
