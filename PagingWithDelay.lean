import PagingWithDelay.Model
import PagingWithDelay.Online
import PagingWithDelay.FIFOOnline
import PagingWithDelay.FIFOFeasible
import PagingWithDelay.Competitive.Final
import PagingWithDelay.LowerBound.Final
import PagingWithDelay.KPlusOne.Final

/-!
# Paging with delay: model and main result

The imported model module contains the trusted definitions. The first theorem below summarizes the paper's claim: there is a feasible online algorithm for paging with delay that is (2k+2)-competitive compared against any feasible schedule, and this algorithm is FIFO with threshold 1.

The second theorem is the converse, "Tightness of the analysis": no threshold makes FIFO better than (2k+2)-competitive. Its proof is in `PagingWithDelay/LowerBound/`: the adversarial instance, the replay of FIFO on it, and the explicit comparator it is measured against. Like the upper bound, it stands on the Lean compiler alone.

The third theorem is the refinement of Section 5 of the write-up: on a universe of exactly `k+1` pages the ratio drops to `2k+1`, for FIFO with the raised threshold `(k+1)/k`, at the price of an additive constant depending only on `k`. Its proof is in `PagingWithDelay/KPlusOne/`, on the generic online-analysis machinery of `PagingWithDelay/Analysis/`.
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
constant it is granted: there is a legal instance of cache size `k` and a
feasible schedule for it whose cost, scaled by the claimed ratio and padded by
the claimed constant, still falls short of what FIFO pays.

Exhibiting a *feasible* comparator is what makes this a statement about the
optimum: its cost bounds the optimum from above, so FIFO also exceeds
`ratio * OPT + additive`.

The additive constant is what lets the comparator pay for reaching the initial
position the paper assumes it starts in — the model starts every cache empty —
and it is why the claim is asymptotic: `ratio` is beaten in the limit of many
runs of the construction, not on one fixed instance. -/
theorem paging_with_delay_lower_bound {Page : Type*} [DecidableEq Page]
    {δ : Cost} (hδ : 0 < δ) {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page)
    (ratio additive : Cost) (hratio : ratio < (2 * k + 2 : ℕ)) :
    ∃ (input : Instance Page) (valid : input.Valid) (comparator : Schedule Page),
      input.cacheSize = k ∧ comparator.Feasible input ∧
        ratio * comparator.totalCost input + additive <
          (FIFO.schedule δ input valid).totalCost input :=
  LowerBound.competitive_ratio_lower_bound hδ hk pages ratio additive hratio

/-- **`(2k+1)`-competitiveness on `k+1` pages.**  For `k ≥ 1`, a cache of size
`k`, and requests drawn from a universe of exactly `k + 1` pages, FIFO with
threshold `(k+1)/k` is online, feasible, and beats the general ratio `2k+2`:
its cost is at most `2k+1` times the cost of any feasible schedule, plus
`(2k+1)²/k`.

Exhibiting the bound against every *feasible* comparator makes this a statement
about the optimum, whose cost the cheapest comparator bounds.

This is Theorem 5.1 of `fifo-upper-bound.tex`, transferred to the model of
`Model.lean`.  The write-up proves it under the convention that FIFO and the
comparator both start from a common full cache, where the bound is
`ALG ≤ (2k+1) OPT` with no additive term; here every cache starts *empty*, and
the additive constant is exactly what that costs.  It is the `(1 + δ)`-image of
`KPlusOne.count_le`, `M ≤ k · OPT + (2k+1)`, whose `2k+1` is the `k+1`
payments made before FIFO's cache is full plus the `k` units of potential the
argument starts with.  The competitive *ratio* — the asymptotic claim — is
`2k+1` either way, which is what the write-up's remark on the two initial-cache
conventions says.

Unlike the `2k+2` bound above this names the algorithm outright, so reading it
means reading `Algorithm.lean` as well as `Model.lean`. -/
theorem paging_with_delay_upper_bound_k_plus_one_pages {Page : Type*} [DecidableEq Page]
    {k : ℕ} (hk : 0 < k) :
    Algorithm.Online (FIFO.schedule (Page := Page) (((k : Cost) + 1) / (k : Cost))) ∧
      ∀ (input : Instance Page) (valid : input.Valid) (pages : Finset Page),
        input.cacheSize = k → pages.card = k + 1 →
        (∀ request ∈ input.requests, request.page ∈ pages) →
          (FIFO.schedule (((k : Cost) + 1) / (k : Cost)) input valid).Feasible input ∧
            ∀ comparator : Schedule Page, comparator.Feasible input →
              (FIFO.schedule (((k : Cost) + 1) / (k : Cost)) input valid).totalCost input ≤
                (2 * k + 1 : ℕ) * comparator.totalCost input +
                  ((2 * k + 1 : ℕ) * (2 * k + 1 : ℕ)) / (k : ℕ) :=
  ⟨FIFO.schedule_online _, fun input valid pages hsize hcard hrequests =>
    ⟨FIFO.schedule_feasible _ input valid, fun comparator feasible =>
      KPlusOne.competitive
        { cacheSize := k, positive := hk, pages := pages, card := hcard
          input := input, valid := valid, size := hsize
          requestPages := hrequests } comparator feasible⟩⟩

end PagingWithDelay
