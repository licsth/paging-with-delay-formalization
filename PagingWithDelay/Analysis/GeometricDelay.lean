import PagingWithDelay.Model

/-!
# Geometrically increasing delay rates

If the rate of each new request is sufficiently larger than the preceding
rate, all older requests together accrue at most `ε` times the current rate.
This is the numerical estimate used by the static offline strategies in the
general lower bound. It does not assume anything about an online algorithm.
-/

namespace PagingWithDelay.Analysis

open scoped BigOperators

/-- Every positive error allowance admits a positive geometric growth rate. -/
theorem exists_rate_growth (ε : Cost) (hε : 0 < ε) :
    ∃ c : Cost, 0 < c ∧ ε + 1 ≤ ε * c := by
  refine ⟨(ε + 1) / ε, div_pos (by positivity) hε, ?_⟩
  exact le_of_eq (mul_div_cancel₀ _ hε.ne').symm

/-- Earlier geometric rates are negligible compared with the current rate. -/
theorem sum_previous_rates_le (c ε : Cost) (hc : ε + 1 ≤ ε * c) (i : ℕ) :
    (∑ j ∈ Finset.range i, c ^ j) ≤ ε * c ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Finset.sum_range_succ, pow_succ]
      calc
        (∑ j ∈ Finset.range i, c ^ j) + c ^ i
            ≤ ε * c ^ i + c ^ i := add_le_add ih le_rfl
        _ = (ε + 1) * c ^ i := by ring
        _ ≤ (ε * c) * c ^ i := by gcongr
        _ = ε * (c ^ i * c) := by ring

/-- Including the current request costs at most `1 + ε` times its rate. -/
theorem sum_rates_le (c ε : Cost) (hc : ε + 1 ≤ ε * c) (i : ℕ) :
    (∑ j ∈ Finset.range (i + 1), c ^ j) ≤ (1 + ε) * c ^ i := by
  rw [Finset.sum_range_succ]
  calc
    _ ≤ ε * c ^ i + c ^ i := add_le_add (sum_previous_rates_le c ε hc i) le_rfl
    _ = (1 + ε) * c ^ i := by ring

/-- The estimate survives arbitrary nonnegative phase lengths, including
zero-length phases. No quotient by the algorithm's delay is necessary. -/
theorem sum_phase_delay_le (c ε : Cost) (hc : ε + 1 ≤ ε * c)
    (duration : ℕ → Time) (n : ℕ) :
    (∑ i ∈ Finset.range n, duration i * (∑ j ∈ Finset.range (i + 1), c ^ j)) ≤
      (1 + ε) * (∑ i ∈ Finset.range n, duration i * c ^ i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ duration i * ((1 + ε) * c ^ i) :=
      mul_le_mul_right (sum_rates_le c ε hc i) _
    _ = (1 + ε) * (duration i * c ^ i) := by ring

/-- A legal linear request with any positive slope. -/
def linearRequest {Page : Type*} (page : Page) (arrival : Time)
    (slope : Cost) (hpos : 0 < slope) : Request Page where
  page := page
  arrival := arrival
  delay := fun wait => slope * wait
  delay_continuous := continuous_const.mul continuous_id
  delay_mono := fun _ _ h => mul_le_mul_right h slope
  delay_zero := mul_zero slope
  delay_unbounded := fun bound => ⟨bound / slope, by
    exact le_of_eq (mul_div_cancel₀ bound hpos.ne').symm⟩

end PagingWithDelay.Analysis
