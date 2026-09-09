import PagingWithDelay.LowerBound.Comparator
import PagingWithDelay.LowerBound.FIFORun

/-!
# Tightness of the analysis

FIFO with threshold `δ` fetches on *every* request of the adversarial
instance, so by the cost accounting `FIFO.algorithmCostClaim` it pays
`(1 + δ) (2k+2)` per run, while the comparator pays `1 + δ`.  Letting the
number of runs grow gives the competitive ratio `2k+2` in the limit, which is
the form the statement takes: no ratio below `2k+2` survives, with any additive
constant.
-/

namespace PagingWithDelay.LowerBound

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- **FIFO faults on every request.**  Every `k+1` consecutive requests are on
distinct pages, and FIFO's cache holds only the `k` most recently fetched
ones, so no request is ever a hit; and arrivals and threshold crossings
alternate, so each fetch serves exactly one request.

The replay is in `PagingWithDelay/LowerBound/FIFORun.lean`: `settled_runs`
walks the event loop from one run to the next, and the settled state it reaches
after the last run records one payment per request. -/
theorem paymentCount_eq {δ : Cost} (hδ : 0 < δ) {k : ℕ} (runs : ℕ)
    (pages : Fin (k + 2) ↪ Page) (hk : 0 < k) :
    FIFO.paymentCount δ (input δ k runs pages) (input_valid δ runs pages hk) =
      runLength k * runs := by
  have h := settled_runs hδ hk pages runs le_rfl
  unfold FIFO.paymentCount
  rw [input_length]
  exact h.payments

/-- The algorithm's cost on the adversarial instance: `(1+δ)` per request. -/
theorem algorithmCost_eq {δ : Cost} (hδ : 0 < δ) {k : ℕ} (runs : ℕ)
    (pages : Fin (k + 2) ↪ Page) (hk : 0 < k) :
    (FIFO.schedule δ (input δ k runs pages) (input_valid δ runs pages hk)).totalCost
        (input δ k runs pages) = (1 + δ) * ((2 * k + 2 : Cost) * runs) := by
  have h := FIFO.algorithmCostClaim δ (input δ k runs pages) (input_valid δ runs pages hk)
  unfold FIFO.AlgorithmCostClaim FIFO.algorithmCost at h
  rw [h, paymentCount_eq hδ runs pages hk]
  push_cast [runLength]
  ring

/-- Enough runs to beat any ratio below `2k+2` and any additive constant. -/
private theorem exists_runs {d bound : Cost} (hd : 0 < d) :
    ∃ runs : ℕ, bound < d * runs := by
  obtain ⟨n, hn⟩ := Archimedean.arch bound hd
  refine ⟨n + 1, lt_of_le_of_lt hn ?_⟩
  rw [nsmul_eq_mul, mul_comm]
  exact mul_lt_mul_of_pos_left (by exact_mod_cast Nat.lt_succ_self n) hd

/-- **Tightness.**  For every threshold `δ`, every cache size `k ≥ 1` and every
page type with at least `k+2` pages, no ratio below `2k+2` holds for FIFO with
threshold `δ > 0`, however large an additive constant it is granted.

`δ = 0` is excluded: there the threshold is met on arrival, so FIFO pays in
arrival order and the timing of the construction — arrivals half a unit before
crossings, with one transposition per run — no longer describes the run. -/
theorem competitive_ratio_lower_bound {δ : Cost} (hδ : 0 < δ) {k : ℕ} (hk : 0 < k)
    (pages : Fin (k + 2) ↪ Page) (ratio additive : Cost)
    (hratio : ratio < (2 * k + 2 : ℕ)) :
    ∃ (input : Instance Page) (valid : input.Valid) (comparator : Schedule Page),
      input.cacheSize = k ∧ comparator.Feasible input ∧
        ratio * comparator.totalCost input + additive <
          (FIFO.schedule δ input valid).totalCost input := by
  have hcast : ((2 * k + 2 : ℕ) : Cost) = 2 * k + 2 := by push_cast; ring
  rw [hcast] at hratio
  -- the slack below the claimed ratio, and enough runs to exhaust the additive constant
  obtain ⟨d, hd, hsum⟩ : ∃ d : Cost, 0 < d ∧ (2 * k + 2 : Cost) = ratio + d :=
    ⟨(2 * k + 2 : Cost) - ratio, tsub_pos_of_lt hratio,
      (add_tsub_cancel_of_le hratio.le).symm⟩
  obtain ⟨runs, hruns⟩ := exists_runs (bound := ratio * (k + 1) + additive) hd
  obtain ⟨comparator, hfeasible, hcost⟩ := exists_comparator δ runs pages hk
  refine ⟨input δ k runs pages, input_valid δ runs pages hk, comparator, rfl, hfeasible, ?_⟩
  rw [algorithmCost_eq hδ runs pages hk, hsum]
  have hone : (1 : Cost) ≤ 1 + δ := le_add_of_nonneg_right (zero_le δ)
  calc ratio * comparator.totalCost (input δ k runs pages) + additive
      ≤ ratio * ((1 + δ) * runs + (k + 1)) + additive := by gcongr
    _ = ratio * ((1 + δ) * runs) + (ratio * (k + 1) + additive) := by ring
    _ < ratio * ((1 + δ) * runs) + d * runs :=
        add_lt_add_of_le_of_lt le_rfl hruns
    _ ≤ ratio * ((1 + δ) * runs) + (1 + δ) * (d * runs) :=
        add_le_add le_rfl (le_mul_of_one_le_left (zero_le _) hone)
    _ = (1 + δ) * ((ratio + d) * runs) := by ring

end
end PagingWithDelay.LowerBound
