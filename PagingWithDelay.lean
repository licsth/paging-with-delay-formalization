import PagingWithDelay.Model
import PagingWithDelay.Online
import PagingWithDelay.FIFOOnline
import PagingWithDelay.FIFOFeasible
import PagingWithDelay.Competitive.Final
import PagingWithDelay.LowerBound.Final
import PagingWithDelay.KPlusOne.Final
import PagingWithDelay.GeneralLowerBound.Adversary
import PagingWithDelay.GeneralLowerBound.Averaging
import PagingWithDelay.GeneralLowerBound.Static
import PagingWithDelay.GeneralLowerBound.Comparators
import PagingWithDelay.GeneralLowerBound.Final

/-!
# Paging with delay: model and main result

The imported model module contains the trusted definitions. The first theorem below summarizes the paper's claim: there is a feasible online algorithm for paging with delay that is (2k+2)-competitive compared against any feasible schedule, and this algorithm is FIFO with threshold 1.

The second theorem is the converse, "Tightness of the analysis": no threshold makes FIFO better than (2k+2)-competitive. Its proof is in `PagingWithDelay/LowerBound/`: the adversarial instance, the replay of FIFO on it, and the explicit comparator it is measured against. Like the upper bound, it stands on the Lean compiler alone.

The third theorem is the refinement of Section 5 of the write-up: on a universe of exactly `k+1` pages the ratio drops to `2k+1`, for FIFO with the raised threshold `(k+1)/k`, at the price of an additive constant depending only on `k`. Its proof is in `PagingWithDelay/KPlusOne/`, on the generic online-analysis machinery of `PagingWithDelay/Analysis/`.

The fourth theorem is the general lower bound of the original paper: on a universe of `k+1` pages, *no* feasible online algorithm is `(2k+1-ε)`-competitive. Its proof is in `PagingWithDelay/GeneralLowerBound/`, and it is unconditional in the algorithm: the request sequence is built adaptively from the algorithm's own behaviour. Together with the third theorem, the ratio `2k+1` on `k+1` pages is tight.
-/

namespace PagingWithDelay

theorem paging_with_delay_upper_bound {Page: Type*} [DecidableEq Page] : ∃ (algorithm : Algorithm Page),
  Algorithm.Online algorithm ∧
    ∀ (input : Instance Page) (valid : input.Valid),
      (algorithm input valid).Feasible input ∧
        ∀ comparator : Schedule Page, comparator.Feasible input →
          (algorithm input valid).totalCost input ≤
            (2 * input.cacheSize + 2 : ℕ) * comparator.totalCost input :=
  ⟨FIFO.schedule 1, FIFO.schedule_online 1, fun input valid =>
    ⟨FIFO.schedule_feasible 1 input valid, Competitive.competitiveRatio input valid⟩⟩

/-- **The analysis is tight.**  For every positive threshold `δ`, every cache size
`k ≥ 1`, and every page type with at least `k + 2` pages, FIFO with threshold
`δ` fails every competitive claim below `2k+2`, however large an additive
constant it is granted. -/
theorem FIFO_lower_bound {Page : Type*} [DecidableEq Page]
    {δ : Cost} (hδ : 0 < δ) {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page)
    (ratio additive : Cost) (hratio : ratio < (2 * k + 2 : ℕ)) :
    ∃ (input : Instance Page) (valid : input.Valid) (comparator : Schedule Page),
      input.cacheSize = k ∧ comparator.Feasible input ∧
        ratio * comparator.totalCost input + additive <
          (FIFO.schedule δ input valid).totalCost input :=
  LowerBound.competitive_ratio_lower_bound hδ hk pages ratio additive hratio

/-- **`(2k+1)`-competitiveness on `k+1` pages.**  For `k ≥ 1`, a cache of size
`k`, there exists an online algorithm that, for requests drawn from a universe
of exactly `k + 1` pages, is feasible and beats the general ratio `2k+2`:
its cost is at most `2k+1` times the cost of any feasible schedule, plus
`(2k+1)²/k`. The proof uses FIFO with threshold `(k+1)/k` as its witness. -/
theorem paging_with_delay_upper_bound_k_plus_one_pages {Page : Type*} [DecidableEq Page]
    {k : ℕ} (hk : 0 < k) :
    ∃ (algorithm : Algorithm Page), Algorithm.Online algorithm ∧
      ∀ (input : Instance Page) (valid : input.Valid) (pages : Finset Page),
        input.cacheSize = k → pages.card = k + 1 →
        (∀ request ∈ input.requests, request.page ∈ pages) →
          (algorithm input valid).Feasible input ∧
            ∀ comparator : Schedule Page, comparator.Feasible input →
              (algorithm input valid).totalCost input ≤
                (2 * k + 1 : ℕ) * comparator.totalCost input +
                  ((2 * k + 1 : ℕ) * (2 * k + 1 : ℕ)) / (k : ℕ) :=
  ⟨FIFO.schedule (((k : Cost) + 1) / (k : Cost)),
    FIFO.schedule_online _, fun input valid pages hsize hcard hrequests =>
    ⟨FIFO.schedule_feasible _ input valid, fun comparator feasible =>
      KPlusOne.competitive
        { cacheSize := k, positive := hk, pages := pages, card := hcard
          input := input, valid := valid, size := hsize
          requestPages := hrequests } comparator feasible⟩⟩

/-- **The general lower bound.**  For `k ≥ 1` and a universe of exactly `k + 1`
pages, every feasible online algorithm fails every competitive claim below
`2k+1`, however large an additive constant it is granted.  The adversarial
input requests only pages from `pages` and is built adaptively from the
algorithm's own run, so no property of the algorithm beyond onlineness and
feasibility is used. -/
theorem paging_with_delay_general_lower_bound {Page : Type*} [DecidableEq Page]
    {k : ℕ} (hk : 0 < k) (pages : Fin (k + 1) ↪ Page)
    (algorithm : Algorithm Page) (online : Algorithm.Online algorithm)
    (feasible : ∀ (input : Instance Page) (valid : input.Valid),
      (algorithm input valid).Feasible input)
    (ratio additive : Cost) (hratio : ratio < (2 * k + 1 : ℕ)) :
    ∃ (input : Instance Page) (valid : input.Valid) (comparator : Schedule Page),
      input.cacheSize = k ∧
      (∀ request ∈ input.requests, request.page ∈ Finset.univ.map pages) ∧
      comparator.Feasible input ∧
        ratio * comparator.totalCost input + additive <
          (algorithm input valid).totalCost input :=
  GeneralLowerBound.competitive_ratio_lower_bound online feasible hk
    (Finset.univ.map pages) (by simp) ratio additive hratio

end PagingWithDelay
