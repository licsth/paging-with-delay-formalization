import PagingWithDelay.KPlusOne.Interval
import PagingWithDelay.Competitive.AlgorithmCost
import PagingWithDelay.PageUniverse

/-!
# Summation and the `(2k+1)` bound

Summing the interval inequality over the payments after the `(k+1)`-st, the
potential telescopes and the comparator's per-interval costs add up to at most
its total cost.  What comes out is `M ≤ k · OPT + 2k + 1`, and with
`ALG = (1 + δ) M` at `δ = (k+1)/k` this is Theorem 5.1 of
`fifo-upper-bound.tex`.
-/

namespace PagingWithDelay.KPlusOne

open PagingWithDelay

variable {Page : Type*} [DecidableEq Page]

noncomputable section

variable {S : Setup Page} {comparator : Schedule Page}

/-- The comparator's costs over the accounted intervals do not exceed its
total cost: the intervals are disjoint and its delay is spent once. -/
theorem sum_intervalCost_le (feasible : comparator.Feasible S.input) (a b : ℕ) (hab : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, intervalCost S comparator i ≤ comparator.totalCost S.input := by
  have hfetch : ∑ i ∈ Finset.Ico a b,
      ((eventIndex S comparator (i + 1) - eventIndex S comparator i : ℕ) : Cost) ≤
      (comparator.fetchCount : Cost) := by
    rw [← Nat.cast_sum]
    refine Nat.cast_le.mpr ?_
    rw [Analysis.sum_Ico_increment_nat eventIndex_monotone hab]
    exact le_trans (Nat.sub_le _ _) (Analysis.eventCount_le_length comparator _)
  have hdelay : ∑ i ∈ Finset.Ico a b,
      Analysis.delayIncrement comparator S.input (S.timeAt i) (S.timeAt (i + 1)) ≤
      comparator.totalDelay S.input :=
    Analysis.sum_delayIncrement_le feasible S.timeAt S.timeAt_mono hab
  unfold intervalCost
  rw [Finset.sum_add_distrib]
  exact add_le_add hfetch hdelay

/-- The potential never exceeds the cache size. -/
theorem potential_le (i : ℕ) (hi : i + 1 ≤ S.count) :
    potential S comparator i ≤ S.cacheSize := by
  unfold potential
  refine le_trans (Analysis.rank_le_length _ _) ?_
  rw [S.queue_length hi]
  exact min_le_left _ _

/-- **`M ≤ k · OPT + 2k + 1`.**  The paper's summation, with the additive term
coming from the first `k + 1` payments and the initial potential. -/
theorem count_le (feasible : comparator.Feasible S.input) :
    (S.count : Cost) ≤
      (S.cacheSize : Cost) * comparator.totalCost S.input + (2 * S.cacheSize + 1 : ℕ) := by
  by_cases hsmall : S.count ≤ 2 * S.cacheSize + 1
  · refine le_trans ?_ (le_add_self)
    exact_mod_cast hsmall
  push_neg at hsmall
  have hbig : S.cacheSize + 2 ≤ S.count := by omega
  have hstep : ∀ i, S.cacheSize ≤ i → i < S.count - 1 →
      (1 : Cost) + (potential S comparator (i + 1) : Cost) ≤
        (S.cacheSize : Cost) * intervalCost S comparator i +
          (potential S comparator i : Cost) := by
    intro i hi hlt
    exact interval_bound feasible hi (by omega)
  have hmain := Analysis.potential_argument (Φ := potential S comparator)
    (Δ := intervalCost S comparator) (c := (S.cacheSize : Cost))
    (a := S.cacheSize) (b := S.count - 1) (by omega) hstep
  have hinit : (potential S comparator S.cacheSize : Cost) ≤ (S.cacheSize : Cost) := by
    exact_mod_cast potential_le (S := S) (comparator := comparator) S.cacheSize (by omega)
  have hsum := sum_intervalCost_le feasible S.cacheSize (S.count - 1) (by omega)
  have hcount : ((S.count - 1 - S.cacheSize : ℕ) : Cost) ≤
      (S.cacheSize : Cost) * comparator.totalCost S.input + (S.cacheSize : Cost) := by
    calc ((S.count - 1 - S.cacheSize : ℕ) : Cost)
        ≤ ((S.count - 1 - S.cacheSize : ℕ) : Cost) +
            (potential S comparator (S.count - 1) : Cost) := le_self_add
      _ ≤ (S.cacheSize : Cost) * (∑ i ∈ Finset.Ico S.cacheSize (S.count - 1),
            intervalCost S comparator i) + (potential S comparator S.cacheSize : Cost) := hmain
      _ ≤ (S.cacheSize : Cost) * comparator.totalCost S.input + (S.cacheSize : Cost) :=
          add_le_add (mul_le_mul_right hsum _) hinit
  have hsplit : (S.count : Cost) =
      ((S.count - 1 - S.cacheSize : ℕ) : Cost) + ((S.cacheSize + 1 : ℕ) : Cost) := by
    rw [← Nat.cast_add]
    congr 1
    omega
  rw [hsplit]
  calc ((S.count - 1 - S.cacheSize : ℕ) : Cost) + ((S.cacheSize + 1 : ℕ) : Cost)
      ≤ ((S.cacheSize : Cost) * comparator.totalCost S.input + (S.cacheSize : Cost)) +
        ((S.cacheSize + 1 : ℕ) : Cost) := add_le_add_left hcount _
    _ = (S.cacheSize : Cost) * comparator.totalCost S.input + (2 * S.cacheSize + 1 : ℕ) := by
        push_cast
        ring

/-- **Theorem 5.1** in the empty-cache model.  On `k + 1` pages, FIFO with
threshold `(k+1)/k` is `(2k+1)`-competitive, up to an additive constant that is
exactly the price of starting from an empty cache: `count_le` loses `k+1`
payments before the cache is full and `k` units of potential, and `1 + δ`
turns that into `(2k+1)²/k`.

Under the write-up's convention — FIFO and the comparator starting from a
common full cache — the same summation has no loss to account for and gives
`ALG ≤ (2k+1) OPT` outright.  That convention cannot be stated against
`Model.lean`, whose caches all start empty. -/
theorem competitive (S : Setup Page) (comparator : Schedule Page)
    (feasible : comparator.Feasible S.input) :
    (FIFO.schedule S.threshold S.input S.valid).totalCost S.input ≤
      (2 * S.cacheSize + 1 : ℕ) * comparator.totalCost S.input +
        ((2 * S.cacheSize + 1 : ℕ) * (2 * S.cacheSize + 1 : ℕ)) / (S.cacheSize : ℕ) := by
  have hk := S.positive
  have hn : (S.cacheSize : Cost) ≠ 0 := S.cacheSize_ne_zero
  have hcost : (FIFO.schedule S.threshold S.input S.valid).totalCost S.input =
      (1 + S.threshold) * (S.count : Cost) := by
    have := FIFO.algorithmCostClaim S.threshold S.input S.valid
    unfold FIFO.AlgorithmCostClaim FIFO.algorithmCost at this
    rw [this]
    rfl
  have hthreshold : (1 : Cost) + S.threshold =
      (2 * (S.cacheSize : Cost) + 1) / (S.cacheSize : Cost) := by
    unfold Setup.threshold
    field_simp
    ring
  have hmul : (1 + S.threshold) * (S.cacheSize : Cost) = (2 * S.cacheSize + 1 : ℕ) := by
    have h := S.cacheSize_mul_threshold
    push_cast
    calc (1 + S.threshold) * (S.cacheSize : Cost)
        = (S.cacheSize : Cost) + (S.cacheSize : Cost) * S.threshold := by ring
      _ = (S.cacheSize : Cost) + ((S.cacheSize : Cost) + 1) := by rw [h]
      _ = 2 * (S.cacheSize : Cost) + 1 := by ring
  rw [hcost]
  calc (1 + S.threshold) * (S.count : Cost)
      ≤ (1 + S.threshold) *
        ((S.cacheSize : Cost) * comparator.totalCost S.input + (2 * S.cacheSize + 1 : ℕ)) :=
        mul_le_mul_right (count_le feasible) _
    _ = ((1 + S.threshold) * (S.cacheSize : Cost)) * comparator.totalCost S.input +
        (1 + S.threshold) * (2 * S.cacheSize + 1 : ℕ) := by ring
    _ = (2 * S.cacheSize + 1 : ℕ) * comparator.totalCost S.input +
        (1 + S.threshold) * (2 * S.cacheSize + 1 : ℕ) := by rw [hmul]
    _ = (2 * S.cacheSize + 1 : ℕ) * comparator.totalCost S.input +
        ((2 * S.cacheSize + 1 : ℕ) * (2 * S.cacheSize + 1 : ℕ)) / (S.cacheSize : ℕ) := by
        rw [hthreshold]
        push_cast
        rw [div_mul_eq_mul_div]

end

/-- The `k+1`-page bound as the public theorem states it: the hypothesis is a
bound on the input's own page universe, and the universe of exactly `k+1` pages
required by `Setup` is recovered from it.  The embedding supplies the pages
such a universe needs when the input uses fewer of them. -/
theorem competitive_of_pageUniverse {k : ℕ} (hk : 0 < k) (pages : Fin (k + 1) ↪ Page)
    (input : Instance Page) (valid : input.Valid) (hsize : input.cacheSize = k)
    (huniverse : input.pageUniverse.card ≤ k + 1)
    (comparator : Schedule Page) (feasible : comparator.Feasible input) :
    (FIFO.schedule (((k : Cost) + 1) / (k : Cost)) input valid).totalCost input ≤
      (2 * k + 1 : ℕ) * comparator.totalCost input +
        ((2 * k + 1 : ℕ) * (2 * k + 1 : ℕ)) / (k : ℕ) := by
  obtain ⟨cover, hcard, hrequests⟩ := input.exists_universe_card_eq pages huniverse
  exact competitive
    { cacheSize := k, positive := hk, pages := cover, card := hcard
      input := input, valid := valid, size := hsize
      requestPages := hrequests } comparator feasible

end PagingWithDelay.KPlusOne