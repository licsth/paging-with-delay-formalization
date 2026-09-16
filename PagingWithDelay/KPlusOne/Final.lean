import PagingWithDelay.RankPotential.Final
import PagingWithDelay.PageUniverse

/-!
# The `(2k+1)` bound on `k+1` pages

The write-up derives its improvement on a universe of `k+1` pages from the
same payment accounting as the general bound, with the stronger offline
potential change: at an offline fetch that evicts a page outside FIFO's cache,
`ΔΦ ≥ 1` rather than `ΔΦ ≥ 0`, because on `k+1` pages the evicted page is the
one page outside FIFO's cache, so the fetched page is inside it and
contributes a rank of at least `1` (`gain_assoc_ge_succ`).  The accounting
then charges only `k` per offline fetch (`payment_accounting_k_plus_one`),
and at `δ = (k+1)/k` both coefficients are `k`: `M ≤ k·OPT` and
`ALG = (1+δ)·M ≤ (2k+1)·OPT` (`competitive`).
-/

namespace PagingWithDelay.KPlusOne

open PagingWithDelay Analysis RankPotential

variable {Page : Type*} [DecidableEq Page]

noncomputable section

variable {S : Setup Page} {comparator : Schedule Page}

/-- **On `k+1` pages, the page fetched into FIFO's cache's complement is
FIFO's cache.**  A page of the universe other than the one page outside the
FIFO cache is in the FIFO cache. -/
theorem mem_queue_of_ne (huniverse : S.input.pageUniverse.card ≤ S.cacheSize + 1)
    {j : ℕ} (hj : j ≤ S.count) {p f : Page} (hp : p ∈ S.input.pageUniverse)
    (hpq : p ∉ S.queue j) (hf : f ∈ S.input.pageUniverse) (hfp : f ≠ p) : f ∈ S.queue j := by
  classical
  by_contra hnot
  -- `queue j`, `p` and `f` are `k + 2` distinct pages of the universe
  have hsub : insert f (insert p (S.queue j).toFinset) ⊆ S.input.pageUniverse := by
    intro q hq
    simp only [Finset.mem_insert, List.mem_toFinset] at hq
    rcases hq with rfl | rfl | hq
    · exact hf
    · exact hp
    · exact S.queue_subset_pageUniverse hj hq
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, List.mem_toFinset, not_or]
        exact ⟨hfp, hnot⟩),
    Finset.card_insert_of_notMem (by rwa [List.mem_toFinset]),
    List.toFinset_card_of_nodup (S.queue_nodup hj), S.queue_length hj] at hcard
  omega

/-- **Potential changes, offline, on `k+1` pages.**  An offline event that
evicts a page outside FIFO's cache raises the potential by at least one: its
gain is at least `k + 1`. -/
theorem gainAt_ge_succ_of_evicted_outside
    (huniverse : S.input.pageUniverse.card ≤ S.cacheSize + 1)
    {j n : ℕ} (hj : j ≤ S.count) {p : Page} (hV : p ∈ S.input.pageUniverse)
    (hp : p ∈ Analysis.lazyCache S.cacheSize S.input.pageUniverse comparator n)
    (hp' : p ∉ Analysis.lazyCache S.cacheSize S.input.pageUniverse comparator (n + 1))
    (hnot : p ∉ S.queue j) :
    S.cacheSize + 1 ≤ gainAt S comparator j n := by
  set L := Analysis.lazyCache S.cacheSize S.input.pageUniverse comparator with hL
  obtain ⟨f, hfV, hfnot, hfmem⟩ := Analysis.exists_fetched_of_evicted n hp hp'
  have hfp : f ≠ p := fun h => hp' (h ▸ hfmem)
  have hfq : f ∈ S.queue j := mem_queue_of_ne huniverse hj hV hnot hfV hfp
  -- the new lazy cache contains the old one minus `p`, plus `f`
  have hsub : insert f ((L n).erase p) ⊆ L (n + 1) := by
    intro q hq
    rw [Finset.mem_insert, Finset.mem_erase] at hq
    rcases hq with rfl | ⟨hqp, hq⟩
    · exact hfmem
    · by_contra hq'
      exact hqp (Finset.mem_singleton.mp
        (Analysis.sdiff_lazyCache_succ_subset_singleton n hp hp' (Finset.mem_sdiff.mpr ⟨hq, hq'⟩)))
  have hrank : 1 ≤ rank (S.queue j) f := one_le_rank_of_mem hfq
  have hstep : rankPotential (S.queue j) (insert f ((L n).erase p)) =
      rankPotential (S.queue j) (L n) + rank (S.queue j) f := by
    rw [rankPotential_insert_of_mem _ (fun h => hfnot (Finset.mem_of_mem_erase h)) hfq,
      rankPotential_erase_of_not_mem _ _ hnot]
  have hmono := rankPotential_mono (S.queue j) hsub
  have hspec := gainAt_spec (comparator := comparator) hj n
  rw [← hL] at hspec
  omega

/-- The stronger case-2 gain of the `k+1`-page setting, for the associated
events of the accounting. -/
theorem gain_assoc_ge_succ
    (huniverse : S.input.pageUniverse.card ≤ S.cacheSize + 1)
    {i : ℕ} (hi : i < S.count) (h : Dropped S comparator i) :
    S.cacheSize + 1 ≤ gainAt S comparator (assoc S comparator i).1 (assoc S comparator i).2 := by
  obtain ⟨hj, hjlow, hjhigh, hlow, hhigh, hmem, hnot⟩ := assoc_spec hi h
  have := pageAt_not_mem_queue_of_mem_window hi hlow hhigh hjlow hjhigh
  exact gainAt_ge_succ_of_evicted_outside huniverse hj.le
    (S.pageAt_mem_pageUniverse hi) hmem hnot this.2

/-- **Payment accounting on `k+1` pages**: `M ≤ k·S + ((k+1)/δ)·D`. -/
theorem paymentCount_le_k_plus_one (feasible : comparator.Feasible S.input)
    (huniverse : S.input.pageUniverse.card ≤ S.cacheSize + 1) :
    (S.count : Cost) ≤
      (S.cacheSize : ℕ) * comparator.fetchCount +
        ((S.cacheSize + 1 : ℕ) / S.threshold) * comparator.totalDelay S.input :=
  paymentCount_le_of_gain feasible (c := S.cacheSize) (g := S.cacheSize + 1) (by ring) le_rfl
    (fun i hi h => gain_assoc_ge_succ huniverse hi h)

/-- The setup of FIFO with threshold `(k+1)/k` on a valid instance with cache
size `k ≥ 1`. -/
def setup {k : ℕ} (hk : 0 < k) (input : Instance Page) (valid : input.Valid)
    (hsize : input.cacheSize = k) : Setup Page where
  cacheSize := k
  positive := hk
  threshold := ((k : Cost) + 1) / (k : Cost)
  threshold_pos := div_pos (by positivity) (by exact_mod_cast hk)
  input := input
  valid := valid
  size := hsize

/-- **The `k+1`-page theorem.**  On `k + 1` pages, FIFO with threshold
`(k+1)/k` is `(2k+1)`-competitive with no additive constant: `M ≤ k·OPT` and
`(1 + δ)·k = 2k + 1`. -/
theorem competitive_of_pageUniverse {k : ℕ} (hk : 0 < k) (pages : Fin (k + 1) ↪ Page)
    (input : Instance Page) (valid : input.Valid) (hsize : input.cacheSize = k)
    (huniverse : input.pageUniverse.card ≤ k + 1)
    (comparator : Schedule Page) (feasible : comparator.Feasible input) :
    (FIFO.schedule (((k : Cost) + 1) / (k : Cost)) input valid).totalCost input ≤
      (2 * k + 1 : ℕ) * comparator.totalCost input := by
  have _ := pages
  set S := setup hk input valid hsize with hS
  have hk' : (k : Cost) ≠ 0 := by exact_mod_cast hk.ne'
  have hM := paymentCount_le_k_plus_one (S := S) feasible huniverse
  have hcost := FIFO.algorithmCostClaim S.threshold input valid
  unfold FIFO.AlgorithmCostClaim FIFO.algorithmCost at hcost
  change (FIFO.schedule S.threshold input valid).totalCost input ≤ _
  rw [hcost]
  have hcount : (FIFO.paymentCount S.threshold input valid : Cost) = (S.count : Cost) := rfl
  rw [hcount]
  have hcoef : ((k + 1 : ℕ) : Cost) / (((k : Cost) + 1) / (k : Cost)) = k := by
    push_cast
    field_simp
  have hM' : (S.count : Cost) ≤
      (k : Cost) * (comparator.fetchCount + comparator.totalDelay input) := by
    change (S.count : Cost) ≤ (k : Cost) * comparator.fetchCount +
      ((k + 1 : ℕ) : Cost) / (((k : Cost) + 1) / (k : Cost)) * comparator.totalDelay input at hM
    rw [hcoef] at hM
    rw [mul_add]
    exact hM
  calc (1 + S.threshold) * (S.count : Cost)
      ≤ (1 + S.threshold) * ((k : Cost) * (comparator.fetchCount + comparator.totalDelay input)) :=
        mul_le_mul_right hM' _
    _ = ((1 + S.threshold) * k) * comparator.totalCost input := by
        unfold Schedule.totalCost; ring
    _ = (2 * k + 1 : ℕ) * comparator.totalCost input := by
        congr 1
        change (1 + ((k : Cost) + 1) / (k : Cost)) * k = _
        push_cast
        field_simp
        ring

end

end PagingWithDelay.KPlusOne
