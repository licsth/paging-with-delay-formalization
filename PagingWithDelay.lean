import Model
import Algorithm
import Proofs.FIFO.Online
import Proofs.FIFO.Nonclairvoyant
import Proofs.RankPotential.Final
import Proofs.KPlusOne.Final
import Proofs.LowerBound.Final
import Proofs.GeneralLowerBound.Final
import Proofs.DeadlineUpperBound.Final
import Proofs.DeadlineLowerBound.Final

/-!
# Paging with delay: model and main result

The definitions are in `Model.lean`. `Checks/StatementChecks.lean` unfolds each statement below into an explicit one about comparator schedules.

1. FIFO with threshold `1` is nonclairvoyant, online and strictly `(2k+2)`-competitive (`Proofs/RankPotential/`).
2. No positive threshold makes FIFO better than `(2k+2)`-competitive (`Proofs/LowerBound/`).
3. On at most `k+1` pages, FIFO with threshold `(k+1)/k` is strictly `(2k+1)`-competitive (`Proofs/KPlusOne/`).
4. On `k+1` pages, no online algorithm is better than `(2k+1)`-competitive (`Proofs/GeneralLowerBound/`).
5. For paging with deadlines, deadline-triggered FIFO is nonclairvoyant, online and strictly `(k+1)`-competitive (`Proofs/DeadlineUpperBound/`).
6. For paging with deadlines on at most `k+1` pages, deadline-triggered FIFO is strictly `k`-competitive (`Proofs/DeadlineUpperBound/`).
7. For paging with deadlines on `k+2` pages, no online algorithm is better than `(k+1/2)`-competitive (`Proofs/DeadlineLowerBound/`).
-/

namespace PagingWithDelay

/-- **`(2k+2)`-competitiveness.** There is a nonclairvoyant, online, strictly `(2k+2)`-competitive algorithm: FIFO with threshold `1`. -/
theorem paging_with_delay_upper_bound {Page : Type*} [DecidableEq Page] :
    ∃ algorithm : Algorithm Page, algorithm.Nonclairvoyant ∧ algorithm.Online ∧
      algorithm.StrictlyCompetitive fun k => 2 * k + 2 :=
  ⟨FIFO.algorithm fun _ => 1, FIFO.algorithm_nonclairvoyant _, FIFO.algorithm_online _,
    RankPotential.strictlyCompetitive⟩

/-- **The analysis is tight.** For every threshold `δ > 0`, FIFO is not `ratio`-competitive if `ratio k < 2k+2` for some `k ≥ 1`, given at least `k + 2` pages. -/
theorem FIFO_lower_bound {Page : Type*} [DecidableEq Page]
    {δ : Cost} (hδ : 0 < δ) {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page)
    {ratio : ℕ → Cost} (hratio : ratio k < 2 * k + 2) :
    ¬ (FIFO.algorithm (Page := Page) fun _ => δ).Competitive ratio :=
  LowerBound.not_competitive hδ hk pages hratio

/-- **`(2k+1)`-competitiveness on `k+1` pages.** There is a nonclairvoyant, online algorithm that is strictly `(2k+1)`-competitive on inputs using at most `k + 1` pages: FIFO with threshold `(k+1)/k`. -/
theorem paging_with_delay_upper_bound_k_plus_one_pages {Page : Type*} [DecidableEq Page] :
    ∃ algorithm : Algorithm Page, algorithm.Nonclairvoyant ∧ algorithm.Online ∧
      algorithm.StrictlyCompetitive (fun k => 2 * k + 1)
        fun input => input.pageUniverse.card ≤ input.cacheSize + 1 :=
  ⟨FIFO.algorithm fun k => ((k : Cost) + 1) / k,
    FIFO.algorithm_nonclairvoyant _, FIFO.algorithm_online _, KPlusOne.strictlyCompetitive⟩

/-- **The general lower bound.** No online algorithm is `ratio`-competitive on inputs using at most `k + 1` pages if `ratio k < 2k+1` for some `k ≥ 1`. -/
theorem paging_with_delay_general_lower_bound {Page : Type*} [DecidableEq Page]
    {k : ℕ} (hk : 0 < k) (pages : Fin (k + 1) ↪ Page)
    {algorithm : Algorithm Page} (online : algorithm.Online)
    {ratio : ℕ → Cost} (hratio : ratio k < 2 * k + 1) :
    ¬ algorithm.Competitive ratio fun input => input.pageUniverse.card ≤ input.cacheSize + 1 :=
  GeneralLowerBound.not_competitive hk pages online hratio

/-- **`(k+1)`-competitiveness for paging with deadlines.** There is a nonclairvoyant, online deadline algorithm that is strictly `(k+1)`-competitive: deadline-triggered FIFO. -/
theorem paging_with_delay_deadline_upper_bound {Page : Type*} [DecidableEq Page] :
    ∃ algorithm : DeadlineAlgorithm Page, algorithm.Nonclairvoyant ∧ algorithm.Online ∧
      algorithm.StrictlyCompetitive fun k => k + 1 :=
  ⟨FIFO.deadlineAlgorithm, FIFO.deadlineAlgorithm_nonclairvoyant, FIFO.deadlineAlgorithm_online,
    DeadlineUpperBound.strictlyCompetitive⟩

/-- **`k`-competitiveness for paging with deadlines on `k+1` pages.** There is a nonclairvoyant, online deadline algorithm that is strictly `k`-competitive on inputs using at most `k + 1` pages: deadline-triggered FIFO. -/
theorem paging_with_delay_deadline_upper_bound_k_plus_one_pages {Page : Type*} [DecidableEq Page] :
    ∃ algorithm : DeadlineAlgorithm Page, algorithm.Nonclairvoyant ∧ algorithm.Online ∧
      algorithm.StrictlyCompetitive (fun k => k)
        fun input => input.pageUniverse.card ≤ input.cacheSize + 1 :=
  ⟨FIFO.deadlineAlgorithm, FIFO.deadlineAlgorithm_nonclairvoyant, FIFO.deadlineAlgorithm_online,
    DeadlineUpperBound.strictlyCompetitive_k_plus_one⟩

/-- **The `k+1/2` lower bound for paging with deadlines.** No online deadline algorithm is `ratio`-competitive if `ratio k < k + 1/2` for some `k ≥ 1`, given at least `k + 2` pages. -/
theorem paging_with_delay_deadline_lower_bound {Page : Type*} [DecidableEq Page]
    {k : ℕ} (hk : 1 ≤ k) (pages : Fin (k + 2) ↪ Page)
    {algorithm : DeadlineAlgorithm Page} (online : algorithm.Online)
    {ratio : ℕ → Cost} (hratio : 2 * ratio k < 2 * k + 1) :
    ¬ algorithm.Competitive ratio :=
  DeadlineLowerBound.not_competitive hk pages online hratio

end PagingWithDelay
