import PagingWithDelay.Model
import PagingWithDelay.Online
import PagingWithDelay.FIFOOnline
import PagingWithDelay.FIFOFeasible
import PagingWithDelay.Competitive.Final
import PagingWithDelay.LowerBound.Final

/-!
# Paging with delay: model and main result

The imported model module contains the trusted definitions. The first theorem below summarizes the paper's claim: there is a feasible online algorithm for paging with delay that is (2k+2)-competitive compared against any feasible schedule, and this algorithm is FIFO with threshold 1.

The second theorem is the converse, "Tightness of the analysis": no threshold makes FIFO better than (2k+2)-competitive. Its proof is in `PagingWithDelay/LowerBound/`: the adversarial instance, the replay of FIFO on it, and the explicit comparator it is measured against. Like the upper bound, it stands on the Lean compiler alone.
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

end PagingWithDelay
