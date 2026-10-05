import Proofs.DeadlineLowerBound.Loop
import Proofs.Basic.PageUniverse

/-!
# The `k + 1/2` lower bound for deadline-shaped delays

Everything comes together here.  For a page set of size `k + 2` and any
feasible online algorithm, `Loop.exists_run` builds an input on which

* the algorithm pays at least one unit per request (`Online.length_le_totalCost`,
  through the misses and the separation the run maintains);
* the certificate supplies a feasible comparator of cost at most
  `m + 1` (`Bridge.certificate_totalCost_le`) — the construction starts at
  time `0` from the initial cache, so no start-up fetches are needed; and
* the certificate's budget obeys `(2k+1) m ≤ 2T + 2k` (`PhaseCount`, through
  the potential the run maintains).

`PhaseCount.no_ratio_below_k_add_half` turns those three into the statement
that no ratio below `k + 1/2` survives.  `exists_input_quantitative` states
them directly, as the write-up's theorem does: for every `N ≥ 1` there is an
input with `ALG ≥ N` and `OPT ≤ (2N + 2k)/(2k+1) + 1`.

`competitive_ratio_lower_bound_pageUniverse` is the form the public theorem
quotes: the page restriction is a bound on `Instance.pageUniverse` of the input
produced, and the delay curves are written out rather than named.  The bound is
`≤ k + 2` and not `= k + 2` because the adversary is not obliged to touch every
page it is allowed: which pages it asks for is decided by the algorithm's own
evictions.
-/

namespace PagingWithDelay.DeadlineLowerBound

open Finset

noncomputable section

variable {Page : Type*} [DecidableEq Page]

/-- **The lower bound.**  Every feasible online algorithm on `k + 2` pages
fails every competitive claim below `k + 1/2`, already on inputs whose delay
curves are of deadline form.  The hypothesis `2 * ratio < 2 * k + 1` says
`ratio < k + 1/2` without dividing. -/
theorem competitive_ratio_lower_bound (algorithm : Algorithm Page)
    (online : algorithm.Online)
    {k : ℕ} (hk : 1 ≤ k) {V : Finset Page} (hcard : V.card = k + 2)
    (ratio additive : Cost) (hratio : 2 * ratio < 2 * (k : Cost) + 1) :
    ∃ (input : Instance Page) (comparator : Schedule Page),
      input.cacheSize = k ∧
      (∀ request ∈ input.requests, IsDeadlineShaped request) ∧
      (∀ page ∈ input.initialCache, page ∈ V) ∧
      (∀ request ∈ input.requests, request.page ∈ V) ∧
      comparator.Feasible input ∧
      (∀ request ∈ input.requests, comparator.requestCost request = 0) ∧
        ratio * comparator.totalCost input + additive <
          (algorithm input).totalCost input := by
  classical
  obtain ⟨steps, hsteps⟩ :=
    PhaseCount.no_ratio_below_k_add_half k ratio additive 1 hratio
  obtain ⟨c, d, hc, hd, hcd, run, hrunSteps⟩ :=
    exists_run algorithm online hk hcard steps
  -- the algorithm pays at least one unit for every request
  have halg : ((run.input.requests.length : ℕ) : Cost) ≤
      (algorithm run.input).totalCost run.input :=
    length_le_totalCost _ (algorithm.feasible _) run.chargeWindow run.penalty
      run.misses run.ordered
  have hlength : (steps : Cost) ≤ ((run.input.requests.length : ℕ) : Cost) := by
    have : steps ≤ run.input.requests.length := by
      rw [run.lengthEq, hrunSteps]
      omega
    exact_mod_cast this
  -- the certificate supplies the comparator
  obtain ⟨z, hz⟩ := run.cert.cheap_nonempty
  have hzV : z ∈ V := (run.cert.cheap_mem_V hz).1
  have hzc : z ≠ run.state.distinguished := (run.cert.cheap_mem_V hz).2
  obtain ⟨comparator, hfeasible, hcost, hcomparatorDelay⟩ :=
    certificate_totalCost_le run.cert hz
      (PhaseCount.refill_nonempty hcard hk run.cert.distinguished_mem hzV
        (fun heq => hzc heq.symm))
      run.size (PhaseCount.card_refill hcard hc hd hcd)
      run.deadline run.startEq run.free run.link
  -- the certificate's budget is small
  have hbudget : (2 * k + 1) * run.state.budget ≤ 2 * steps + 2 * k := by
    have hpotential := run.stateValid.potential_le
    have hbound := run.potentialBound
    rw [hrunSteps] at hbound
    omega
  refine ⟨run.input, comparator, run.size, run.shaped, run.initialPages, run.pages,
    hfeasible, hcomparatorDelay, ?_⟩
  · refine hsteps (run.state.budget : Cost) _ (comparator.totalCost run.input)
      (hlength.trans halg) ?_ ?_
    · exact_mod_cast hbudget
    · exact_mod_cast hcost

/-- The lower bound as the public theorem states it: the universe restriction is
a bound on the page universe of the input the construction produces, the `k+2`
pages it may request come from the given embedding, and the comparator serves
every request at no delay cost.

The last conjunct is what carries the deadline reading.  The construction's
delay curves are zero inside a window and then grow, so a schedule with no delay
cost is one that serves every request inside its window — a schedule that misses
no deadline.  Stating that about the comparator, rather than stating the shape
of the curves, keeps the theorem free of any interpretation of what a "deadline"
is. -/
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
  obtain ⟨input, comparator, hsize, _, hinitial, hpages, hfeasible, hdelay, hcost⟩ :=
    competitive_ratio_lower_bound algorithm online hk
      (V := Finset.univ.map pages) (by simp) ratio additive hratio
  exact ⟨input, comparator, hsize,
    (Instance.card_pageUniverse_le hinitial hpages).trans_eq (by simp), hfeasible, hdelay, hcost⟩


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
  classical
  set V : Finset Page := Finset.univ.map pages with hV
  have hcard : V.card = k + 2 := by simp [hV]
  obtain ⟨c, d, hc, hd, hcd, run, hrunSteps⟩ :=
    exists_run algorithm online hk hcard (N - 1)
  have hlengthN : run.input.requests.length = N := by
    rw [run.lengthEq, hrunSteps]
    omega
  -- the algorithm pays at least one unit for every request
  have halg : ((run.input.requests.length : ℕ) : Cost) ≤
      (algorithm run.input).totalCost run.input :=
    length_le_totalCost _ (algorithm.feasible _) run.chargeWindow run.penalty
      run.misses run.ordered
  -- the certificate supplies the comparator
  obtain ⟨z, hz⟩ := run.cert.cheap_nonempty
  have hzV : z ∈ V := (run.cert.cheap_mem_V hz).1
  have hzc : z ≠ run.state.distinguished := (run.cert.cheap_mem_V hz).2
  obtain ⟨comparator, hfeasible, hcost, hcomparatorDelay⟩ :=
    certificate_totalCost_le run.cert hz
      (PhaseCount.refill_nonempty hcard hk run.cert.distinguished_mem hzV
        (fun heq => hzc heq.symm))
      run.size (PhaseCount.card_refill hcard hc hd hcd)
      run.deadline run.startEq run.free run.link
  -- the certificate's budget is small: `(2k+1) B ≤ 2(N-1) + 2k`
  have hbudget : (2 * k + 1) * run.state.budget ≤ 2 * (N - 1) + 2 * k := by
    have hpotential := run.stateValid.potential_le
    have hbound := run.potentialBound
    rw [hrunSteps] at hbound
    omega
  have hnat : (2 * k + 1) * (run.state.budget + 1) ≤ 2 * N + 2 * k + (2 * k + 1) := by
    rw [Nat.mul_succ]
    omega
  refine ⟨run.input, comparator, run.size,
    (Instance.card_pageUniverse_le run.initialPages run.pages).trans_eq hcard, hlengthN,
    hfeasible, hcomparatorDelay, by rw [← hlengthN]; exact halg, ?_⟩
  calc (2 * k + 1 : Cost) * comparator.totalCost run.input
      ≤ (2 * k + 1 : Cost) * ((run.state.budget + 1 : ℕ) : Cost) := by gcongr
    _ = (((2 * k + 1) * (run.state.budget + 1) : ℕ) : Cost) := by push_cast; ring
    _ ≤ ((2 * N + 2 * k + (2 * k + 1) : ℕ) : Cost) := by exact_mod_cast hnat
    _ = 2 * N + 2 * k + (2 * k + 1) := by push_cast; ring

end
end PagingWithDelay.DeadlineLowerBound
