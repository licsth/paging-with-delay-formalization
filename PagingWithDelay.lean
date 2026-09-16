import PagingWithDelay.Model
import PagingWithDelay.PageUniverse
import PagingWithDelay.Online
import PagingWithDelay.Nonclairvoyant
import PagingWithDelay.FIFOOnline
import PagingWithDelay.FIFONonclairvoyant
import PagingWithDelay.FIFOFeasible
import PagingWithDelay.Competitive.Final
import PagingWithDelay.LowerBound.Final
import PagingWithDelay.KPlusOne.Final
import PagingWithDelay.GeneralLowerBound.Adversary
import PagingWithDelay.GeneralLowerBound.Averaging
import PagingWithDelay.GeneralLowerBound.Static
import PagingWithDelay.GeneralLowerBound.Comparators
import PagingWithDelay.GeneralLowerBound.Final
import PagingWithDelay.DeadlineLowerBound.Final

/-!
# Paging with delay: model and main result

The imported model module contains the trusted definitions. The first theorem below summarizes the main claim: there is a feasible online algorithm for paging with delay that is (2k+2)-competitive compared against any feasible schedule, and this algorithm is FIFO with threshold 1. The algorithm is in fact nonclairvoyant, which is more than online: it never consults the delay a request has yet to accrue, only the delay accrued so far. That is stated as the first conjunct of the first and third theorems, and it implies onlineness (`Algorithm.Nonclairvoyant.online`), which the same theorems keep stating separately.

The second theorem is the converse, "Tightness of the analysis": no threshold makes FIFO better than (2k+2)-competitive. Its proof is in `PagingWithDelay/LowerBound/`: the adversarial instance, the replay of FIFO on it, and the explicit comparator it is measured against. Like the upper bound, it stands on the Lean compiler alone.

The third theorem is the refinement of the first theorem: on a universe of exactly `k+1` pages the ratio drops to `2k+1`, for FIFO with the raised threshold `(k+1)/k`. Its proof is in `PagingWithDelay/KPlusOne/`, on the generic online-analysis machinery of `PagingWithDelay/Analysis/`.

The fourth theorem is the general lower bound of the original paper: on a universe of `k+1` pages, *no* feasible online algorithm is `(2k+1-ε)`-competitive. Its proof is in `PagingWithDelay/GeneralLowerBound/`, and it is unconditional in the algorithm: the request sequence is built adaptively from the algorithm's own behaviour. Together with the third theorem, the ratio `2k+1` on `k+1` pages is tight.

The fifth theorem restricts to the deadline setting rather than shrinking the page universe: on at most `k+2` distinct pages, no feasible online algorithm is `(k+1/2-ε)`-competitive against a comparator that serves every request at zero delay cost. The statement specialises to the hard-deadline problem. Its proof is in `PagingWithDelay/DeadlineLowerBound/`, and it is again unconditional in the algorithm. It is a different restriction from the fourth theorem, and neither implies the other: there the comparator is allowed to pay additional cost to delay a request further, and the universe has `k+1` pages, here the comparator has deadline constraints and the universe has `k+2` pages.
-/

namespace PagingWithDelay

theorem paging_with_delay_upper_bound {Page: Type*} [DecidableEq Page] : ∃ (algorithm : Algorithm Page),
  Algorithm.Nonclairvoyant algorithm ∧ Algorithm.Online algorithm ∧ Algorithm.Feasible algorithm ∧
    ∀ (input : Instance Page) (valid : input.Valid),
        ∀ comparator : Schedule Page, comparator.Feasible input →
          (algorithm input valid).totalCost input ≤
            (2 * input.cacheSize + 2 : ℕ) * comparator.totalCost input :=
  ⟨FIFO.schedule 1, FIFO.schedule_nonclairvoyant 1, FIFO.schedule_online 1, FIFO.feasible 1,
    fun input valid => Competitive.competitiveRatio input valid⟩

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
`k`, and a page type with at least `k + 1` pages, there exists an online
algorithm that, on every input using at most `k + 1` distinct pages — the `k`
initially cached ones and at most one more — is feasible and beats the general
ratio `2k+2`: its cost is at most `2k+1` times the cost of any feasible
schedule, with no additive constant. The proof uses FIFO with threshold
`(k+1)/k` as its witness. -/
theorem paging_with_delay_upper_bound_k_plus_one_pages {Page : Type*} [DecidableEq Page]
    {k : ℕ} (hk : 0 < k) :
    ∃ (algorithm : Algorithm Page), Algorithm.Nonclairvoyant algorithm ∧
      Algorithm.Online algorithm ∧ Algorithm.Feasible algorithm ∧
      ∀ (input : Instance Page) (valid : input.Valid), (Fin (k + 1) ↪ Page) →
        input.cacheSize = k → input.pageUniverse.card ≤ k + 1 →
          ∀ comparator : Schedule Page, comparator.Feasible input →
            (algorithm input valid).totalCost input ≤
              (2 * k + 1 : ℕ) * comparator.totalCost input :=
  ⟨FIFO.schedule (((k : Cost) + 1) / (k : Cost)), FIFO.schedule_nonclairvoyant _,
    FIFO.schedule_online _, FIFO.feasible _, fun input valid pages hsize huniverse =>
    KPlusOne.competitive_of_pageUniverse hk pages input valid hsize huniverse⟩

/-- **The general lower bound.**  For `k ≥ 1` and a page type with at least
`k + 1` pages, every feasible online algorithm fails every competitive claim below
`2k+1`, however large an additive constant it is granted.  The embedding `pages`
only supplies the `k + 1` pages the construction uses, for its initial cache
and its requests. -/
theorem paging_with_delay_general_lower_bound {Page : Type*} [DecidableEq Page]
    {k : ℕ} (hk : 0 < k) (pages : Fin (k + 1) ↪ Page)
    (algorithm : Algorithm Page)
    (online : Algorithm.Online algorithm) (feasible : Algorithm.Feasible algorithm)
    (ratio additive : Cost) (hratio : ratio < (2 * k + 1 : ℕ)) :
    ∃ (input : Instance Page) (valid : input.Valid) (comparator : Schedule Page),
      input.cacheSize = k ∧
      input.pageUniverse.card ≤ k + 1 ∧
      comparator.Feasible input ∧
        ratio * comparator.totalCost input + additive <
          (algorithm input valid).totalCost input :=
  GeneralLowerBound.competitive_ratio_lower_bound_pageUniverse online feasible hk pages
    ratio additive hratio

/-- **The `k+1/2` lower bound for deadline delays.**  For `k ≥ 1` and a page type
with at least `k+2` pages, every feasible online algorithm fails every competitive
claim below `k+1/2`, however large an additive constant it is granted,
on an input involving at most `k+2` distinct pages, initial cache included. The
embedding `pages` only supplies the `k+2` pages the construction may use. The
hypothesis `2 * ratio < 2 * k + 1` says `ratio < k + 1/2` without dividing.

The theorem is about deadlines in the sense that it certifies that the comparator pays
*no delay cost at all*. The theorem therefore says that even an algorithm allowed to buy
its way out of deadlines cannot beat `k+1/2` against a comparator that never does,
which implies the corresponding bound for the hard-deadline problem.  `StatementChecks.lean`
derives that specialisation. -/
theorem paging_with_delay_deadline_lower_bound {Page : Type*} [DecidableEq Page]
    {k : ℕ} (hk : 1 ≤ k) (pages : Fin (k + 2) ↪ Page)
    (algorithm : Algorithm Page)
    (online : Algorithm.Online algorithm) (feasible : Algorithm.Feasible algorithm)
    (ratio additive : Cost) (hratio : 2 * ratio < 2 * (k : Cost) + 1) :
    ∃ (input : Instance Page) (valid : input.Valid) (comparator : Schedule Page),
      input.cacheSize = k ∧
      input.pageUniverse.card ≤ k + 2 ∧
      comparator.Feasible input ∧
      (∀ request ∈ input.requests, comparator.requestCost request = 0) ∧
        ratio * comparator.totalCost input + additive <
          (algorithm input valid).totalCost input :=
  DeadlineLowerBound.competitive_ratio_lower_bound_pageUniverse online feasible hk pages
    ratio additive hratio

end PagingWithDelay
