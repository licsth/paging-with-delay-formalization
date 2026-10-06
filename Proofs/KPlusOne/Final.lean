import Proofs.RankPotential.Final
import Proofs.Basic.PageUniverse
import Algorithm
import Proofs.Basic.Competitive

/-!
# The `(2k+1)` bound on `k+1` pages

The write-up derives its improvement on a universe of `k+1` pages from the
same payment accounting as the general bound, with the stronger offline
potential change: at an offline fetch that evicts a page outside FIFO's cache,
`ΔΦ ≥ 1` rather than `ΔΦ ≥ 0`, because on `k+1` pages the evicted page is the
one page outside FIFO's cache, so the fetched page is inside it and
contributes a rank of at least `1` (`gain_assoc_ge_succ`); in the write-up's
potential `Φ = ∑_{q ∈ C_ALG \ C_OPT} rank q` this is `ΔΦ ≤ -1`
(`missingPotential_succ_add_one_le_of_evicted_outside`).  The accounting
then charges only `k` per offline fetch (`paymentCount_le_k_plus_one`, and
`payment_accounting_missing_k_plus_one` with the potentials),
and at `δ = (k+1)/k` both coefficients are `k`: `M ≤ k·OPT` and
`ALG = (1+δ)·M ≤ (2k+1)·OPT` (`competitive_of_pageUniverse`).
-/

namespace PagingWithDelay.KPlusOne

open PagingWithDelay Analysis RankPotential

variable {Page : Type*} [DecidableEq Page]

noncomputable section

variable {S : Setup Page} {comparator : Schedule Page}

/-- On `k+1` pages, a page of the universe other than the one page outside
FIFO's cache is in FIFO's cache. -/
theorem mem_queue_of_ne (huniverse : S.input.pageUniverse.card ≤ S.cacheSize + 1)
    {j : ℕ} (hj : j ≤ S.count) {p f : Page} (hp : p ∈ S.input.pageUniverse)
    (hpq : p ∉ S.queue j) (hf : f ∈ S.input.pageUniverse) (hfp : f ≠ p) : f ∈ S.queue j := by
  by_contra hnot
  -- `queue j`, `p` and `f` are `k + 2` distinct pages of the universe
  have hsub : insert f (insert p (S.queue j).toFinset) ⊆ S.input.pageUniverse := by
    simp only [Finset.insert_subset_iff, hf, hp, true_and]
    exact fun q hq => S.queue_subset_pageUniverse hj (List.mem_toFinset.mp hq)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hfp, hnot]),
    Finset.card_insert_of_notMem (by simpa using hpq),
    List.toFinset_card_of_nodup (S.queue_nodup hj), S.queue_length hj] at hcard
  omega

/-- **Potential changes, offline, on `k+1` pages.**  An offline event that
evicts a page outside FIFO's cache raises the potential by at least one: its
gain is at least `k + 1`. -/
theorem gainAt_ge_succ_of_evicted_outside
    (huniverse : S.input.pageUniverse.card ≤ S.cacheSize + 1)
    {j n : ℕ} (hj : j ≤ S.count) {p : Page} (hV : p ∈ S.input.pageUniverse)
    (hp : p ∈ lazy S comparator n) (hp' : p ∉ lazy S comparator (n + 1))
    (hnot : p ∉ S.queue j) :
    S.cacheSize + 1 ≤ gainAt S comparator j n := by
  obtain ⟨f, hfV, hfnot, hfmem⟩ := Analysis.exists_fetched_of_evicted n hp hp'
  have hfq : f ∈ S.queue j := mem_queue_of_ne huniverse hj hV hnot hfV fun h => hp' (h ▸ hfmem)
  -- the new lazy cache contains the old one minus `p`, plus `f`
  have hsub : insert f ((lazy S comparator n).erase p) ⊆ lazy S comparator (n + 1) := by
    refine Finset.insert_subset hfmem fun q hq => ?_
    obtain ⟨hqp, hq⟩ := Finset.mem_erase.mp hq
    by_contra hq'
    exact hqp (Finset.mem_singleton.mp
      (Analysis.sdiff_lazyCache_succ_subset_singleton n hp hp' (Finset.mem_sdiff.mpr ⟨hq, hq'⟩)))
  have hmono := rankPotential_mono (S.queue j) hsub
  rw [rankPotential_insert_of_mem _ (fun h => hfnot (Finset.mem_of_mem_erase h)) hfq,
    rankPotential_erase_of_not_mem _ (lazy S comparator n) hnot] at hmono
  have := one_le_rank_of_mem hfq
  have := gainAt_spec (comparator := comparator) hj n
  omega

/-- The stronger case-2 gain of the `k+1`-page setting, for the associated
events of the accounting. -/
theorem gain_assoc_ge_succ
    (huniverse : S.input.pageUniverse.card ≤ S.cacheSize + 1)
    {i : ℕ} (hi : i < S.count) (h : Dropped S comparator i) :
    S.cacheSize + 1 ≤ gainAt S comparator (assoc S comparator i).1 (assoc S comparator i).2 := by
  obtain ⟨hj, hjlow, hjhigh, hlow, hhigh, hmem, hnot⟩ := assoc_spec hi h
  exact gainAt_ge_succ_of_evicted_outside huniverse hj.le (S.pageAt_mem_pageUniverse hi) hmem hnot
    (pageAt_not_mem_queue_of_mem_window hi hlow hhigh hjlow hjhigh).2

/-- **Potential changes, offline, on `k+1` pages**, in the write-up's potential
`Φ = ∑_{q ∈ C_ALG \ C_OPT} rank q`: an offline event that evicts a page outside
FIFO's cache lowers `Φ` by at least one. -/
theorem missingPotential_succ_add_one_le_of_evicted_outside
    (huniverse : S.input.pageUniverse.card ≤ S.cacheSize + 1)
    {j n : ℕ} (hj : j ≤ S.count) {p : Page} (hV : p ∈ S.input.pageUniverse)
    (hp : p ∈ lazy S comparator n) (hp' : p ∉ lazy S comparator (n + 1))
    (hnot : p ∉ S.queue j) :
    missingPotential (S.queue j) (lazy S comparator (n + 1)) + 1 ≤
      missingPotential (S.queue j) (lazy S comparator n) := by
  have := gainAt_ge_succ_of_evicted_outside huniverse hj hV hp hp' hnot
  have := gainAt_spec (comparator := comparator) hj n
  have := missingPotential_add_rankPotential (S.queue_nodup hj) (lazy S comparator n)
  have := missingPotential_add_rankPotential (S.queue_nodup hj) (lazy S comparator (n + 1))
  omega

/-- **Payment accounting on `k+1` pages** in the write-up's form (with `C_OPT`
and `Φ_final` read as in `RankPotential.payment_accounting_missing`):
`M + Φ_final - Φ_0 ≤ k·S + ((k+1)/δ)·D`, stated additively, with
`Φ = ∑_{q ∈ C_ALG \ C_OPT} rank q`. -/
theorem payment_accounting_missing_k_plus_one (hδ : 0 < S.threshold) (feasible : comparator.Feasible S.input)
    (huniverse : S.input.pageUniverse.card ≤ S.cacheSize + 1) :
    (S.count : Cost) + missing S comparator S.count ≤
      (S.cacheSize : ℕ) * comparator.fetchCount +
        ((S.cacheSize + 1 : ℕ) / S.threshold) * comparator.totalDelay S.input +
        missing S comparator 0 :=
  payment_accounting_missing_of_gain hδ feasible (c := S.cacheSize) (g := S.cacheSize + 1)
    (by ring) le_rfl (fun i hi h => gain_assoc_ge_succ huniverse hi h)

/-- **Payment accounting on `k+1` pages**: `M ≤ k·S + ((k+1)/δ)·D`. -/
theorem paymentCount_le_k_plus_one (hδ : 0 < S.threshold) (feasible : comparator.Feasible S.input)
    (huniverse : S.input.pageUniverse.card ≤ S.cacheSize + 1) :
    (S.count : Cost) ≤
      (S.cacheSize : ℕ) * comparator.fetchCount +
        ((S.cacheSize + 1 : ℕ) / S.threshold) * comparator.totalDelay S.input :=
  paymentCount_le_of_gain hδ feasible (c := S.cacheSize) (g := S.cacheSize + 1) (by ring) le_rfl
    (fun i hi h => gain_assoc_ge_succ huniverse hi h)

/-- **The `k+1`-page theorem.**  On `k + 1` pages, FIFO with threshold
`(k+1)/k` is `(2k+1)`-competitive with no additive constant: `M ≤ k·OPT` and
`(1 + δ)·k = 2k + 1`. -/
theorem competitive_of_pageUniverse (input : Instance Page)
    (huniverse : input.pageUniverse.card ≤ input.cacheSize + 1)
    (comparator : Schedule Page) (feasible : comparator.Feasible input) :
    (FIFO.schedule (.threshold (((input.cacheSize : Cost) + 1) / input.cacheSize)) input).totalCost
        input ≤ (2 * input.cacheSize + 1 : ℕ) * comparator.totalCost input := by
  have hk : (input.cacheSize : Cost) ≠ 0 := by exact_mod_cast input.positiveCapacity.ne'
  have hM := paymentCount_le_k_plus_one (S := ⟨.threshold ((input.cacheSize + 1) / input.cacheSize), input⟩)
    (div_pos (by positivity) (by exact_mod_cast input.positiveCapacity)) feasible huniverse
  have hcoef : ((input.cacheSize + 1 : ℕ) : Cost) / ((input.cacheSize + 1) / input.cacheSize) =
      input.cacheSize := by
    push_cast
    field_simp
  simp only [Setup.threshold, FIFO.Trigger.level_threshold, hcoef] at hM
  refine (totalCost_le_of_paymentCount_le hM).trans_eq ?_
  simp only [Setup.threshold, FIFO.Trigger.level_threshold]
  push_cast
  field_simp
  ring

/-- **The `k+1`-page theorem** in the form `PagingWithDelay.lean` states it:
FIFO with threshold `(k+1)/k` at cache size `k` is strictly `(2k+1)`-competitive
on the inputs using at most `k + 1` pages. -/
theorem strictlyCompetitive :
    (FIFO.algorithm (Page := Page) fun k => ((k : Cost) + 1) / k).StrictlyCompetitive
      (fun k => 2 * k + 1) fun input => input.pageUniverse.card ≤ input.cacheSize + 1 :=
  Algorithm.strictlyCompetitive_of_schedules fun input huniverse comparator feasible => by
    simpa using competitive_of_pageUniverse input huniverse comparator feasible

end

end PagingWithDelay.KPlusOne
