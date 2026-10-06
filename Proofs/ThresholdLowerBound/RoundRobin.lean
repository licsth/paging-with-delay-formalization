import Proofs.ThresholdLowerBound.Payments
import Proofs.GeneralLowerBound.Static
import Proofs.Basic.PageUniverse

/-!
# Small thresholds: round robin on `k + 1` pages

The adversary works on `k + 1` pages and, at times `2, 4, …, 2N`, requests the
page the algorithm does not hold.  Each request's delay rises linearly to the
threshold `δ` within one time unit and then only very slowly (rate `ε`).  A
threshold algorithm pays a fetch and `δ` for every request (`cost_ge`), so
`ALG ≥ (1 + δ) N`.

The comparator is the static strategy of `GeneralLowerBound/Static.lean` whose
hole is a least-requested page: it receives at most `N/(k+1)` requests, each
held until the end at cost at most `δ + ε T`.  With `ε` small this gives
`(k+1) OPT ≤ N δ + (k+1)(k+2)`, so the ratio tends to `(k+1)(1 + 1/δ)`.

The slow rise after `δ`, instead of a plateau, is what the threshold
definition needs: a curve that stays at `δ` would let the algorithm postpone a
fetch and serve two requests with one payment.
-/

namespace PagingWithDelay.ThresholdLowerBound

open Finset

noncomputable section

variable {Page : Type*} [DecidableEq Page]

/-! ## The delay curve -/

/-- Linear growth to `δ` within one time unit, then slow growth at rate `ε`. -/
def rampCurve (δ ε : Cost) (wait : Time) : Cost :=
  min (δ * wait) (δ + ε * (wait - 1))

theorem rampCurve_gt {δ ε : Cost} (hδ : 0 < δ) (hε : 0 < ε) {wait : Time} (hwait : 1 < wait) :
    δ < rampCurve δ ε wait :=
  lt_min (lt_mul_of_one_lt_right hδ hwait)
    (lt_add_of_pos_right _ (mul_pos hε (tsub_pos_of_lt hwait)))

theorem rampCurve_le (δ ε : Cost) (wait : Time) : rampCurve δ ε wait ≤ δ + ε * wait :=
  (min_le_right _ _).trans (by gcongr; exact tsub_le_self)

/-- A request on `page` arriving at `arrival` with the ramp curve. -/
def rampRequest (page : Page) (arrival : Time) {δ ε : Cost} (hδ : 0 < δ) (hε : 0 < ε) :
    Request Page where
  page := page
  arrival := arrival
  delay := rampCurve δ ε
  delay_continuous := by
    unfold rampCurve
    exact (continuous_const.mul continuous_id).min
      (continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const)))
  delay_mono := fun a b hab => min_le_min (by gcongr) (by gcongr)
  delay_zero := by simp [rampCurve]
  delay_unbounded := fun bound => by
    refine ⟨bound / δ + bound / ε + 1, le_min ?_ ?_⟩
    · calc bound = δ * (bound / δ) := (mul_div_cancel₀ _ hδ.ne').symm
        _ ≤ δ * (bound / δ + bound / ε + 1) :=
          by gcongr; exact le_add_right (le_add_right le_rfl)
    · rw [add_tsub_cancel_right]
      calc bound = ε * (bound / ε) := (mul_div_cancel₀ _ hε.ne').symm
        _ ≤ ε * (bound / δ + bound / ε) := by gcongr; exact le_add_self
        _ ≤ δ + ε * (bound / δ + bound / ε) := le_add_self

/-! ## The adaptive input -/

/-- After `n` rounds: `n` ramp requests at times `2, 4, …, 2n` on pages of `V`,
each a miss of the algorithm, with disjoint unit windows. -/
theorem exists_rampInput (algorithm : ThresholdAlgorithm Page) (online : algorithm.Online)
    {k : ℕ} (hk : 1 ≤ k) {V : Finset Page} (hcard : V.card = k + 1)
    {δ ε : Cost} (hδ : 0 < δ) (hε : 0 < ε) (n : ℕ) :
    ∃ input : Instance Page,
      input.cacheSize = k ∧
      (∀ page ∈ input.initialCache, page ∈ V) ∧
      input.requests.length = n ∧
      (∀ r ∈ input.requests, r.page ∈ V ∧ 0 < r.arrival ∧ r.arrival ≤ 2 * (n : Time) ∧
        r.delay = rampCurve δ ε) ∧
      (∀ r ∈ input.requests, r.page ∉ (algorithm.run input).cacheBefore r.arrival) ∧
      input.requests.Pairwise fun first second =>
        first.page ≠ second.page ∨ first.arrival + 1 < second.arrival := by
  induction n with
  | zero =>
      refine ⟨⟨k, V.toList.take k, [], List.Pairwise.nil, hk,
        (Finset.nodup_toList V).sublist (List.take_sublist _ _), by simp [hcard]⟩,
        rfl, fun page hpage => Finset.mem_toList.mp (List.mem_of_mem_take hpage),
        rfl, by simp, by simp, List.Pairwise.nil⟩
  | succ n ih =>
      obtain ⟨input, hsize, hinit, hlen, hreq, hmiss, hsep⟩ := ih
      set arrival : Time := 2 * ((n : Time) + 1) with harrival
      have hcache : ((algorithm.run input).cacheBefore arrival).card < V.card := by
        have := (algorithm.run input).cacheBefore_card_le input (algorithm.feasible input) arrival
        omega
      obtain ⟨page, hpageV, hpage⟩ := Finset.exists_mem_notMem_of_card_lt_card hcache
      set request := rampRequest page arrival hδ hε with hrequest
      have hle : 2 * (n : Time) ≤ arrival := by
        rw [harrival]
        gcongr
        exact le_self_add
      have hlast : ∀ r ∈ input.requests, r.arrival ≤ request.arrival :=
        fun r hr => (hreq r hr).2.2.1.trans hle
      refine ⟨input.appendRequest request hlast, hsize, hinit, ?_, ?_, ?_, ?_⟩
      · simp [Instance.appendRequest, hlen]
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · obtain ⟨h1, h2, h3, h4⟩ := hreq r hr
          exact ⟨h1, h2, h3.trans (by push_cast; exact hle), h4⟩
        · rw [List.mem_singleton.mp hr]
          refine ⟨hpageV, show (0 : Time) < 2 * ((n : Time) + 1) by positivity,
            by push_cast; exact le_rfl, rfl⟩
      · exact DeadlineLowerBound.appendRequest_misses online input request hlast hmiss hpage
      · refine List.pairwise_append.mpr ⟨hsep, by simp, ?_⟩
        intro first hfirst second hsecond
        rw [List.mem_singleton.mp hsecond]
        refine Or.inr ?_
        calc first.arrival + 1 ≤ 2 * (n : Time) + 1 := by gcongr; exact (hreq first hfirst).2.2.1
          _ < 2 * (n : Time) + 2 := by gcongr; exact one_lt_two
          _ = request.arrival := by simp [hrequest, rampRequest, harrival]; ring

/-! ## The bound -/

/-- **Small thresholds.**  On `k + 1` pages the adversary forces `(1 + δ)` per
request on a threshold algorithm, while a static comparator pays about `δ / (k+1)`
per request. -/
theorem exists_input_roundRobin (algorithm : ThresholdAlgorithm Page) (online : algorithm.Online)
    {k : ℕ} (hk : 1 ≤ k) (pages : Fin (k + 1) ↪ Page) (N : ℕ) :
    ∃ (input : Instance Page) (comparator : Schedule Page),
      input.cacheSize = k ∧
      input.pageUniverse.card ≤ k + 1 ∧
      comparator.Feasible input ∧
      (1 + algorithm.threshold k) * N ≤ (algorithm.run input).totalCost input ∧
      (k + 1 : Cost) * comparator.totalCost input ≤
        N * algorithm.threshold k + (k + 1) * (k + 2) := by
  classical
  set δ := algorithm.threshold k with hδdef
  have hδ : 0 < δ := algorithm.threshold_pos k
  set T : Time := 2 * (N : Time) + 2 with hT
  have hTpos : 0 < T := by positivity
  set ε : Cost := 1 / (T * (N + 1)) with hεdef
  have hε : 0 < ε := by positivity
  set V : Finset Page := Finset.univ.map pages with hV
  have hcard : V.card = k + 1 := by simp [hV]
  obtain ⟨input, hsize, hinit, hlen, hreq, hmiss, hsep⟩ :=
    exists_rampInput algorithm online hk hcard hδ hε N
  -- the algorithm pays `1 + δ` per request
  have halg := cost_ge algorithm input (fun _ => 1) hmiss
    (fun r hr wait hwait => by
      rw [hsize, (hreq r hr).2.2.2]
      exact rampCurve_gt hδ hε hwait) hsep
  rw [hsize, hlen] at halg
  -- a least-requested hole
  set count : Page → ℕ := fun p => (input.requests.map Request.page).count p with hcount
  obtain ⟨hole, hholeV, hmin⟩ := V.exists_min_image count ⟨pages 0, by simp [hV]⟩
  have hholeCount : (k + 1) * count hole ≤ N := by
    have hsum : ∑ p ∈ V, count p = N := by
      simpa [hcount, hlen] using Multiset.sum_count_eq_card
        (m := ((input.requests.map Request.page : List Page) : Multiset Page))
        (by simpa using fun r hr => (hreq r hr).1)
    simpa [hcard, hsum] using V.card_nsmul_le_sum count (count hole) hmin
  -- the static comparator with that hole
  have hrequests : ∀ r ∈ input.requests, r.page ∈ V ∧ 0 < r.arrival ∧ r.arrival ≤ T := by
    intro r hr
    obtain ⟨h1, h2, h3, _⟩ := hreq r hr
    exact ⟨h1, h2, h3.trans le_self_add⟩
  set comparator := GeneralLowerBound.staticComparator input.initialCache.toFinset V hole T
  have hfeasible : comparator.Feasible input :=
    GeneralLowerBound.staticComparator_feasible input V hole hholeV (by rw [hcard, hsize]) T
      hrequests
  have hfetch : (comparator.fetchCount : Cost) ≤ k + 1 := by
    exact_mod_cast hcard ▸ GeneralLowerBound.staticComparator_fetchCount_le _ V hole hholeV T
  have hdelay : comparator.totalDelay input ≤ count hole * (δ + ε * T) := by
    calc comparator.totalDelay input
        ≤ ((input.requests.map Request.page).map fun p =>
            if p = hole then δ + ε * T else 0).sum := by
          rw [List.map_map]
          refine List.sum_le_sum fun r hr => ?_
          obtain ⟨h1, h2, h3⟩ := hrequests r hr
          refine (GeneralLowerBound.staticComparator_requestCost_le _ _ _
            (GeneralLowerBound.initialCache_card_le_erase input (hsize ▸ hcard) hholeV) _ r h1 h2
            h3).trans ?_
          dsimp only [Function.comp]
          split
          · rw [(hreq r hr).2.2.2]
            exact (rampCurve_le δ ε _).trans (by gcongr; exact tsub_le_self)
          · exact le_rfl
      _ = count hole * (δ + ε * T) := by
          rw [List.sum_map_eq_nsmul_single hole _ fun p hp _ => if_neg hp, if_pos rfl, nsmul_eq_mul]
  have hεT : (N : Cost) * (ε * T) ≤ 1 := by
    have : ε * T = 1 / ((N : Cost) + 1) := by
      rw [hεdef]
      field_simp
    rw [this, mul_one_div, div_le_one (by positivity)]
    exact le_self_add
  have hcountCast : ((k : Cost) + 1) * count hole ≤ N := by exact_mod_cast hholeCount
  refine ⟨input, comparator, hsize,
    (Instance.card_pageUniverse_le hinit fun r hr => (hreq r hr).1).trans_eq hcard,
    hfeasible, halg, ?_⟩
  calc ((k : Cost) + 1) * comparator.totalCost input
      = (k + 1) * comparator.fetchCount + (k + 1) * comparator.totalDelay input := by
        unfold Schedule.totalCost; ring
    _ ≤ (k + 1) * (k + 1) + (k + 1) * (count hole * (δ + ε * T)) := by gcongr
    _ = (k + 1) * (k + 1) + ((k + 1) * count hole) * (δ + ε * T) := by ring
    _ ≤ (k + 1) * (k + 1) + N * (δ + ε * T) := by gcongr
    _ = N * δ + ((k + 1) * (k + 1) + N * (ε * T)) := by ring
    _ ≤ N * δ + ((k + 1) * (k + 1) + (k + 1)) := by gcongr; exact hεT.trans le_add_self
    _ = N * δ + (k + 1) * (k + 2) := by ring

end
end PagingWithDelay.ThresholdLowerBound
