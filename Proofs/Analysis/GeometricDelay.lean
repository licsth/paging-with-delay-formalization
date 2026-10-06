import Model

/-!
# Geometrically increasing delay rates

Linear delay curves, and a growth rate `c` for every error allowance `ε`
satisfying `ε + 1 ≤ ε c`: if each new rate is `c` times the preceding one, all
older requests together accrue at most `ε` times the current rate.  This is
used by the static offline strategies in the general lower bound.
-/

namespace PagingWithDelay.Analysis

/-- Every positive error allowance admits a positive geometric growth rate. -/
theorem exists_rate_growth (ε : Cost) (hε : 0 < ε) :
    ∃ c : Cost, 0 < c ∧ ε + 1 ≤ ε * c :=
  ⟨(ε + 1) / ε, div_pos (by positivity) hε, (mul_div_cancel₀ _ hε.ne').ge⟩

/-- A legal linear request with any positive slope. -/
def linearRequest {Page : Type*} (page : Page) (arrival : Time)
    (slope : Cost) (hpos : 0 < slope) : Request Page where
  page := page
  arrival := arrival
  delay := fun wait => slope * wait
  delay_continuous := continuous_const.mul continuous_id
  delay_mono := fun _ _ h => mul_le_mul_right h slope
  delay_zero := mul_zero slope
  delay_unbounded := fun bound => ⟨bound / slope, (mul_div_cancel₀ bound hpos.ne').ge⟩

end PagingWithDelay.Analysis
