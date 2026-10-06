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
    δ < rampCurve δ ε wait := by
  refine lt_min ?_ (lt_add_of_pos_right _ (mul_pos hε (tsub_pos_of_lt hwait)))
  calc δ = δ * 1 := (mul_one δ).symm
    _ < δ * wait := mul_lt_mul_of_pos_left hwait hδ

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

/-! ## Counting -/

omit [DecidableEq Page] in
/-- Requests on a fixed page, counted. -/
private theorem sum_ite_eq_count (requests : List (Request Page)) (hole : Page) (x : Cost)
    [DecidablePred fun r : Request Page => r.page = hole] :
    (requests.map fun r => if r.page = hole then x else 0).sum =
      (requests.filter fun r => r.page = hole).length * x := by
  induction requests with
  | nil => simp
  | cons r rest ih =>
      by_cases h : r.page = hole
      · simp [h, ih]; ring
      · simp [h, ih]

/-- Summing the per-page counts over a set containing every requested page
gives the number of requests. -/
private theorem sum_count_eq_length (requests : List (Request Page)) (V : Finset Page)
    (hV : ∀ r ∈ requests, r.page ∈ V) :
    ∑ p ∈ V, (requests.filter fun r => r.page = p).length = requests.length := by
  induction requests with
  | nil => simp
  | cons r rest ih =>
      have hrest := ih fun r' hr' => hV r' (List.mem_cons_of_mem _ hr')
      simp only [List.filter_cons, List.length_cons]
      rw [← hrest]
      have hsplit : ∀ p ∈ V,
          ((if decide (r.page = p) = true then r :: rest.filter (fun r => r.page = p)
            else rest.filter (fun r => r.page = p))).length =
            (if r.page = p then 1 else 0) + (rest.filter fun r => r.page = p).length := by
        intro p _
        by_cases h : r.page = p <;> simp [h, add_comm]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
        Finset.sum_ite_eq V r.page (fun _ => 1), if_pos (hV r (by simp)), add_comm]

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
  set count : Page → ℕ := fun p => (input.requests.filter fun r => r.page = p).length
    with hcount
  obtain ⟨hole, hholeV, hmin⟩ := V.exists_min_image count ⟨pages 0, by simp [hV]⟩
  have hholeCount : (k + 1) * count hole ≤ N := by
    have hsum := sum_count_eq_length input.requests V fun r hr => (hreq r hr).1
    have hnsmul := V.card_nsmul_le_sum count (count hole) hmin
    rw [hcard, smul_eq_mul] at hnsmul
    rw [← hlen, ← hsum]
    exact hnsmul
  -- the static comparator with that hole
  have hrequests : ∀ r ∈ input.requests, r.page ∈ V ∧ 0 < r.arrival ∧ r.arrival ≤ T := by
    intro r hr
    obtain ⟨h1, h2, h3, _⟩ := hreq r hr
    exact ⟨h1, h2, h3.trans le_self_add⟩
  set comparator := GeneralLowerBound.staticComparator input.initialCache.toFinset V hole T
  have hfeasible : comparator.Feasible input :=
    GeneralLowerBound.staticComparator_feasible input V hole hholeV (by rw [hcard, hsize]) T
      hrequests
  have hinitCard : input.initialCache.toFinset.card ≤ (V.erase hole).card := by
    rw [Finset.card_erase_of_mem hholeV, hcard, Nat.add_sub_cancel, ← hsize]
    exact GeneralLowerBound.initialCache_card_le input
  have hfetch : (comparator.fetchCount : Cost) ≤ k + 1 := by
    have := GeneralLowerBound.staticComparator_fetchCount_le input.initialCache.toFinset V hole
      hholeV T
    rw [hcard] at this
    exact_mod_cast this
  have hdelay : comparator.totalDelay input ≤ count hole * (δ + ε * T) := by
    unfold Schedule.totalDelay
    rw [hcount, ← sum_ite_eq_count]
    apply List.sum_le_sum
    intro r hr
    obtain ⟨h1, h2, h3⟩ := hrequests r hr
    refine (GeneralLowerBound.staticComparator_requestCost_le _ _ _ hinitCard _ r h1 h2 h3).trans ?_
    split
    · rw [(hreq r hr).2.2.2]
      exact (rampCurve_le δ ε _).trans (by gcongr; exact tsub_le_self)
    · exact le_rfl
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
    _ ≤ N * δ + ((k + 1) * (k + 1) + 1) := by gcongr
    _ ≤ N * δ + (k + 1) * (k + 2) := by
        gcongr
        have : (1 : Cost) ≤ k + 1 := le_add_self
        calc ((k : Cost) + 1) * (k + 1) + 1 ≤ (k + 1) * (k + 1) + (k + 1) := by gcongr
          _ = (k + 1) * (k + 2) := by ring

end
end PagingWithDelay.ThresholdLowerBound
