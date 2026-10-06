import Proofs.DeadlineLowerBound.Loop
import Proofs.Basic.PageUniverse
import Proofs.Basic.Competitive
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.Linarith

/-!
# The `k + 1/2` lower bound for deadline-shaped delays

Everything comes together here.  For a page set of size `k + 2` and any
online algorithm, `exists_run` builds an input on which

* the algorithm pays at least one unit per request (`length_le_totalCost`,
  through the misses and the separation the run maintains);
* the certificate supplies a feasible comparator of cost at most `m + 1`
  (`certificate_totalCost_le`) — the construction starts at time `0` from the
  initial cache, so no start-up fetches are needed; and
* the certificate's budget obeys `(2k+1) m ≤ 2T + 2k` (`PhaseCount.budget_bound`,
  through the run of certificate operations the construction records).

`exists_input_quantitative` states this as the write-up's theorem does: for
every `N ≥ 1` there is an input with `ALG ≥ N` and `OPT ≤ (2N + 2k)/(2k+1) + 1`.
`no_ratio_below_k_add_half` turns it into the statement that no ratio below
`k + 1/2` survives.

The page restriction is a bound on `Instance.pageUniverse` of the input
produced.  It is `≤ k + 2` and not `= k + 2` because which pages the adversary
asks for is decided by the algorithm's own evictions.
-/

namespace PagingWithDelay.DeadlineLowerBound

open Finset

noncomputable section

variable {Page : Type*} [DecidableEq Page]

/-- The adversarial input together with what the charging argument needs:
every request is a miss on arrival, has accrued a unit of delay by the end of
its charging window, and any two requests ask for different pages or have
disjoint windows.  The comparator serves every request at no delay cost and
pays at most `(2N + 2k)/(2k+1) + 1`. -/
theorem exists_input_charged {algorithm : Algorithm Page}
    (online : algorithm.Online)
    {k : ℕ} (hk : 1 ≤ k) (pages : Fin (k + 2) ↪ Page) {N : ℕ} (hN : 1 ≤ N) :
    ∃ (input : Instance Page) (comparator : Schedule Page) (window : Request Page → Time),
      input.cacheSize = k ∧
      input.pageUniverse.card ≤ k + 2 ∧
      input.requests.length = N ∧
      comparator.Feasible input ∧
      (∀ request ∈ input.requests, comparator.requestCost request = 0) ∧
      (∀ request ∈ input.requests,
        request.page ∉ (algorithm input).cacheBefore request.arrival) ∧
      (∀ request ∈ input.requests, 1 ≤ request.delay (window request)) ∧
      input.requests.Pairwise (fun first second =>
        first.page ≠ second.page ∨ first.arrival + window first < second.arrival) ∧
      (2 * k + 1 : Cost) * comparator.totalCost input ≤ 2 * N + 2 * k + (2 * k + 1) := by
  classical
  have hcard : (Finset.univ.map pages).card = k + 2 := by simp
  obtain ⟨c, d, hc, hd, hcd, run, hsteps⟩ := exists_run online hk hcard (N - 1)
  -- the certificate supplies the comparator
  obtain ⟨z, hz⟩ := run.cert.cheap_nonempty
  obtain ⟨hzV, hzc⟩ := run.cert.cheap_mem_V hz
  obtain ⟨comparator, hfeasible, hcost, hdelay⟩ := certificate_totalCost_le run.cert hz
    (PhaseCount.refill_nonempty hcard hk run.cert.distinguished_mem hzV hzc.symm)
    run.deadline run.startEq run.free run.link
  -- the certificate's budget is small: `(2k+1) B ≤ 2(N-1) + 2k`
  have hbudget := PhaseCount.budget_bound hcard hk hc hd hcd (hsteps ▸ run.history)
  have hnat : (2 * k + 1) * (run.state.budget + 1) ≤ 2 * N + 2 * k + (2 * k + 1) := by
    rw [Nat.mul_succ]
    omega
  refine ⟨run.input, comparator, run.chargeWindow, run.size,
    (Instance.card_pageUniverse_le run.initialPages run.pages).trans_eq hcard,
    by rw [run.lengthEq, hsteps]; omega, hfeasible, hdelay, run.misses, run.penalty,
    run.ordered, ?_⟩
  calc (2 * k + 1 : Cost) * comparator.totalCost run.input
      ≤ (2 * k + 1 : Cost) * ((run.state.budget + 1 : ℕ) : Cost) := by gcongr
    _ ≤ 2 * N + 2 * k + (2 * k + 1) := by exact_mod_cast hnat

/-- **The quantitative form of the write-up's theorem.**  For every `N ≥ 1`
there is an input of `N` requests on at most `k + 2` pages on which the
algorithm pays at least `N`, while a feasible comparator that serves every
request at no delay cost pays at most `(2N + 2k)/(2k+1) + 1`, stated without
dividing as `(2k+1)·OPT ≤ 2N + 2k + (2k+1)`. -/
theorem exists_input_quantitative {algorithm : Algorithm Page}
    (online : algorithm.Online)
    {k : ℕ} (hk : 1 ≤ k) (pages : Fin (k + 2) ↪ Page) {N : ℕ} (hN : 1 ≤ N) :
    ∃ (input : Instance Page) (comparator : Schedule Page),
      input.cacheSize = k ∧
      input.pageUniverse.card ≤ k + 2 ∧
      input.requests.length = N ∧
      comparator.Feasible input ∧
      (∀ request ∈ input.requests, comparator.requestCost request = 0) ∧
      (N : Cost) ≤ (algorithm input).totalCost input ∧
      (2 * k + 1 : Cost) * comparator.totalCost input ≤ 2 * N + 2 * k + (2 * k + 1) := by
  obtain ⟨input, comparator, window, hsize, hcard, hlength, hfeasible, hdelay, hmisses,
    hpenalty, hordered, hcost⟩ := exists_input_charged online hk pages hN
  refine ⟨input, comparator, hsize, hcard, hlength, hfeasible, hdelay, ?_, hcost⟩
  rw [← hlength]
  exact length_le_totalCost _ (algorithm.feasible _) window hpenalty hmisses hordered

/-- **The arithmetic endgame.**  `ALG ≥ N` and `(2k+1)·OPT ≤ 2N + 2k + (2k+1)`
leave no competitive ratio below `k + 1/2` once `N` is large, whatever additive
constant is granted.  The hypothesis `2 * r < 2 * k + 1` is `r < k + 1/2`
written without division. -/
theorem no_ratio_below_k_add_half (k : ℕ) (r β : Cost) (hr : 2 * r < 2 * (k : Cost) + 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ alg opt : Cost, (N : Cost) ≤ alg →
      (2 * k + 1 : Cost) * opt ≤ 2 * N + 2 * k + (2 * k + 1) → r * opt + β < alg := by
  have hrreal : 2 * (r : ℝ) < 2 * k + 1 := by exact_mod_cast hr
  have hpos : (0 : ℝ) < 2 * k + 1 - 2 * r := by linarith
  obtain ⟨T, hT⟩ :=
    exists_nat_gt (((4 * (k : ℝ) + 1) * r + (2 * k + 1) * β) / (2 * k + 1 - 2 * r))
  rw [div_lt_iff₀ hpos] at hT
  refine ⟨T + 1, by omega, fun alg opt halg hopt => ?_⟩
  have hoptreal : (2 * k + 1 : ℝ) * opt ≤ 2 * (T + 1) + 2 * k + (2 * k + 1) := by
    exact_mod_cast hopt
  have halgreal : (T + 1 : ℝ) ≤ alg := by exact_mod_cast halg
  have hkey : (2 * k + 1 : ℝ) * (r * opt + β) < (2 * k + 1) * alg := by
    nlinarith [mul_le_mul_of_nonneg_left hoptreal r.coe_nonneg]
  exact_mod_cast lt_of_mul_lt_mul_left hkey (by positivity)

/-- The lower bound as the public theorem states it: the universe restriction
is a bound on the page universe of the input the construction produces, the
`k+2` pages it may request come from the given embedding, and the comparator
serves every request at no delay cost.

The last conjunct is what carries the deadline reading.  The construction's
delay curves are zero inside a window and then grow, so a schedule with no
delay cost is one that serves every request inside its window — a schedule that
misses no deadline. -/
theorem competitive_ratio_lower_bound_pageUniverse {algorithm : Algorithm Page}
    (online : algorithm.Online)
    {k : ℕ} (hk : 1 ≤ k) (pages : Fin (k + 2) ↪ Page)
    (ratio additive : Cost) (hratio : 2 * ratio < 2 * (k : Cost) + 1) :
    ∃ (input : Instance Page) (comparator : Schedule Page),
      input.cacheSize = k ∧
      input.pageUniverse.card ≤ k + 2 ∧
      comparator.Feasible input ∧
      (∀ request ∈ input.requests, comparator.requestCost request = 0) ∧
        ratio * comparator.totalCost input + additive <
          (algorithm input).totalCost input := by
  obtain ⟨N, hN, hbound⟩ := no_ratio_below_k_add_half k ratio additive hratio
  obtain ⟨input, comparator, hsize, hcard, -, hfeasible, hdelay, halg, hcost⟩ :=
    exists_input_quantitative online hk pages hN
  exact ⟨input, comparator, hsize, hcard, hfeasible, hdelay, hbound _ _ halg hcost⟩

/-- **The `k+1/2` lower bound** in the form `PagingWithDelay.lean` states it:
for online deadline algorithms, against deadline algorithms. -/
theorem not_competitive {k : ℕ} (hk : 1 ≤ k) (pages : Fin (k + 2) ↪ Page)
    {algorithm : DeadlineAlgorithm Page} (online : algorithm.Online)
    {ratio : ℕ → Cost} (hratio : 2 * ratio k < 2 * k + 1) :
    ¬ algorithm.Competitive ratio :=
  DeadlineAlgorithm.not_competitive_of_schedules fun additive => by
    obtain ⟨input, comparator, hsize, -, hfeasible, hmeets, hcost⟩ :=
      competitive_ratio_lower_bound_pageUniverse online hk pages (ratio k) (additive k) hratio
    subst hsize
    exact ⟨input, comparator, trivial, hfeasible, hmeets, hcost⟩

end
end PagingWithDelay.DeadlineLowerBound
