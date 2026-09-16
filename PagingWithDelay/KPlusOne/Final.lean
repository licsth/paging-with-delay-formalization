import PagingWithDelay.KPlusOne.Interval
import PagingWithDelay.Competitive.AlgorithmCost
import PagingWithDelay.PageUniverse

/-!
# Summation and the `(2k+1)` bound

Summing the interval inequality over all `M` payments, the potential
telescopes and the comparator's per-interval costs add up to at most its total
cost.  The initial potential is zero: the comparator's hole is the one page of
the universe outside the common initial cache, which FIFO does not hold
either.  What comes out is `M ≤ k · OPT`, and with `ALG = (1 + δ) M` at
`δ = (k+1)/k` this is the `k+1`-page theorem of the write-up, with no
additive constant.
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
    exact le_trans (Nat.sub_le _ _) (eventIndex_le_length b)
  have hdelay : ∑ i ∈ Finset.Ico a b,
      Analysis.delayIncrement comparator S.input (S.boundary i) (S.boundary (i + 1)) ≤
      comparator.totalDelay S.input :=
    Analysis.sum_delayIncrement_le feasible S.boundary S.boundary_mono hab
  unfold intervalCost
  rw [Finset.sum_add_distrib]
  exact add_le_add hfetch hdelay

/-- FIFO's initial queue is the instance's initial cache. -/
theorem queue_zero (S : Setup Page) : S.queue 0 = S.input.initialCache := by
  simp [Setup.queue, FIFO.recentPages]

/-- **The initial potential is zero.**  Both caches start as `C₀`, so the
comparator's hole is the one page of the universe FIFO does not hold. -/
theorem potential_zero (feasible : comparator.Feasible S.input) :
    potential S comparator 0 = 0 := by
  unfold potential holeAt eventIndex
  have hnot : hole S comparator 0 ∉ S.queue 0 := by
    intro hmem
    apply hole_notMem_cache feasible 0
    rw [Analysis.cacheAfterCount_zero, feasible.initialCache, List.mem_toFinset]
    rwa [queue_zero] at hmem
  simp [Analysis.rank, hnot]

/-- **`M ≤ k · OPT`.**  The paper's summation over all `M` accounting
intervals, starting from the maximal (here: zero) potential. -/
theorem count_le (feasible : comparator.Feasible S.input) :
    (S.count : Cost) ≤ (S.cacheSize : Cost) * comparator.totalCost S.input := by
  have hstep : ∀ i, 0 ≤ i → i < S.count →
      (1 : Cost) + (potential S comparator (i + 1) : Cost) ≤
        (S.cacheSize : Cost) * intervalCost S comparator i +
          (potential S comparator i : Cost) := by
    intro i _ hlt
    exact interval_bound feasible hlt
  have hmain := Analysis.potential_argument (Φ := potential S comparator)
    (Δ := intervalCost S comparator) (c := (S.cacheSize : Cost))
    (a := 0) (b := S.count) (Nat.zero_le _) hstep
  rw [potential_zero feasible, Nat.sub_zero] at hmain
  have hsum := sum_intervalCost_le feasible 0 S.count (Nat.zero_le _)
  calc (S.count : Cost)
      ≤ (S.count : Cost) + (potential S comparator S.count : Cost) := le_self_add
    _ ≤ (S.cacheSize : Cost) * (∑ i ∈ Finset.Ico 0 S.count, intervalCost S comparator i) +
          ((0 : ℕ) : Cost) := hmain
    _ = (S.cacheSize : Cost) * (∑ i ∈ Finset.Ico 0 S.count, intervalCost S comparator i) := by
          simp
    _ ≤ (S.cacheSize : Cost) * comparator.totalCost S.input := mul_le_mul_right hsum _

/-- **The `k+1`-page theorem.**  On `k + 1` pages, FIFO with threshold
`(k+1)/k` is `(2k+1)`-competitive with no additive constant: `ALG = (1 + δ) M`
and `M ≤ k · OPT`, with `(1 + δ) k = 2k + 1`. -/
theorem competitive (S : Setup Page) (comparator : Schedule Page)
    (feasible : comparator.Feasible S.input) :
    (FIFO.schedule S.threshold S.input S.valid).totalCost S.input ≤
      (2 * S.cacheSize + 1 : ℕ) * comparator.totalCost S.input := by
  have hcost : (FIFO.schedule S.threshold S.input S.valid).totalCost S.input =
      (1 + S.threshold) * (S.count : Cost) := by
    have := FIFO.algorithmCostClaim S.threshold S.input S.valid
    unfold FIFO.AlgorithmCostClaim FIFO.algorithmCost at this
    rw [this]
    rfl
  have hmul : (1 + S.threshold) * (S.cacheSize : Cost) = (2 * S.cacheSize + 1 : ℕ) := by
    have h := S.cacheSize_mul_threshold
    push_cast
    calc (1 + S.threshold) * (S.cacheSize : Cost)
        = (S.cacheSize : Cost) + (S.cacheSize : Cost) * S.threshold := by ring
      _ = (S.cacheSize : Cost) + ((S.cacheSize : Cost) + 1) := by rw [h]
      _ = 2 * (S.cacheSize : Cost) + 1 := by ring
  rw [hcost]
  calc (1 + S.threshold) * (S.count : Cost)
      ≤ (1 + S.threshold) * ((S.cacheSize : Cost) * comparator.totalCost S.input) :=
        mul_le_mul_right (count_le feasible) _
    _ = ((1 + S.threshold) * (S.cacheSize : Cost)) * comparator.totalCost S.input := by ring
    _ = (2 * S.cacheSize + 1 : ℕ) * comparator.totalCost S.input := by rw [hmul]

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
      (2 * k + 1 : ℕ) * comparator.totalCost input := by
  obtain ⟨cover, hcard, hinitial, hrequests⟩ := input.exists_universe_card_eq pages huniverse
  exact competitive
    { cacheSize := k, positive := hk, pages := cover, card := hcard
      input := input, valid := valid, size := hsize
      initialPages := hinitial, requestPages := hrequests } comparator feasible

end PagingWithDelay.KPlusOne
