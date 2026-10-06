import Proofs.ThresholdLowerBound.Payments
import Proofs.DeadlineLowerBound.Final

/-!
# Large thresholds: the deadline adversary, scaled

The deadline adversary of `Proofs/DeadlineLowerBound/` charges a unit of delay
to every request that is not fetched inside its window.  Against a threshold
algorithm with threshold `δ ≥ 1` a unit is not enough, so the delay curves are
scaled by `c = δ + 1`: run the adversary against the online algorithm that
answers an input with the threshold algorithm's schedule for the scaled input.
After scaling, every request has accrued more than `δ` once its window has
passed, so the threshold algorithm fetches it inside its window
(`ThresholdLowerBound.cost_ge`), and pays `1 + δ` per request.  The comparator
serves every request at no delay, so scaling does not change its cost.
-/

namespace PagingWithDelay

open Finset

noncomputable section

variable {Page : Type*} [DecidableEq Page]

namespace ThresholdLowerBound

/-! ## Scaling delay curves -/

/-- The request with its delay curve multiplied by `c`. -/
def scaleRequest (c : Cost) (hc : 0 < c) (request : Request Page) : Request Page where
  page := request.page
  arrival := request.arrival
  delay := fun wait => c * request.delay wait
  delay_continuous := continuous_const.mul request.delay_continuous
  delay_mono := fun _ _ h => mul_le_mul_right (request.delay_mono h) c
  delay_zero := by simp [request.delay_zero]
  delay_unbounded := fun bound => by
    obtain ⟨wait, hwait⟩ := request.delay_unbounded (bound / c)
    refine ⟨wait, ?_⟩
    calc bound = c * (bound / c) := by rw [mul_div_cancel₀ _ (ne_of_gt hc)]
      _ ≤ c * request.delay wait := mul_le_mul_right hwait c

omit [DecidableEq Page] in
theorem scaleRequest_inv (c : Cost) (hc : 0 < c) (request : Request Page) :
    scaleRequest c⁻¹ (inv_pos.mpr hc) (scaleRequest c hc request) = request := by
  cases request
  simp only [scaleRequest, Request.mk.injEq, true_and]
  funext wait
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]

/-- The instance with every delay curve multiplied by `c`. -/
def scaleInstance (c : Cost) (hc : 0 < c) (input : Instance Page) : Instance Page :=
  { input with
    requests := input.requests.map (scaleRequest c hc)
    chronological := List.pairwise_map.mpr input.chronological }

omit [DecidableEq Page] in
theorem scaleInstance_upTo (c : Cost) (hc : 0 < c) (input : Instance Page) (t : Time) :
    (scaleInstance c hc input).upTo t = scaleInstance c hc (input.upTo t) := by
  simp only [scaleInstance, Instance.upTo, Instance.mk.injEq, true_and, List.filter_map]
  rfl

/-- Service only depends on pages and arrivals, so scaling multiplies each
request's cost by `c`. -/
theorem requestCost_scale (schedule : Schedule Page) (c : Cost) (hc : 0 < c)
    (request : Request Page) :
    schedule.requestCost (scaleRequest c hc request) = c * schedule.requestCost request :=
  rfl

theorem serviceCandidates_scale (schedule : Schedule Page) (c : Cost) (hc : 0 < c)
    (request : Request Page) :
    schedule.serviceCandidates (scaleRequest c hc request) =
      schedule.serviceCandidates request :=
  rfl

theorem feasible_scale_iff (schedule : Schedule Page) (c : Cost) (hc : 0 < c)
    (input : Instance Page) :
    schedule.Feasible (scaleInstance c hc input) ↔ schedule.Feasible input := by
  constructor
  · intro h
    exact ⟨h.initialCache, h.chronological, h.validTransitions, h.capacity,
      fun request hrequest => by
        rw [← serviceCandidates_scale schedule c hc]
        exact h.eventuallyServed _ (List.mem_map_of_mem hrequest)⟩
  · intro h
    refine ⟨h.initialCache, h.chronological, h.validTransitions, h.capacity, ?_⟩
    intro request hrequest
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hrequest
    rw [serviceCandidates_scale]
    exact h.eventuallyServed original horiginal

/-- The algorithm that answers an input with `algorithm`'s schedule for the
scaled input.  It is online when `algorithm` is. -/
def scaledAlgorithm (algorithm : Algorithm Page) (c : Cost) (hc : 0 < c) : Algorithm Page where
  run input := algorithm (scaleInstance c hc input)
  feasible input := (feasible_scale_iff _ c hc input).mp (algorithm.feasible _)

theorem scaledAlgorithm_online {algorithm : Algorithm Page} (online : algorithm.Online)
    (c : Cost) (hc : 0 < c) : (scaledAlgorithm algorithm c hc).Online := by
  refine ⟨fun first second t h => ?_⟩
  apply online.prefixDetermined
  rw [scaleInstance_upTo, scaleInstance_upTo, h]

theorem pageUniverse_scale (c : Cost) (hc : 0 < c) (input : Instance Page) :
    (scaleInstance c hc input).pageUniverse = input.pageUniverse := by
  simp only [Instance.pageUniverse, scaleInstance, List.map_map]
  rfl

/-! ## The large-threshold bound -/

/-- **Large thresholds.**  For every `N ≥ 1` there is an input on at most
`k + 2` pages on which a threshold algorithm with threshold `δ` pays at least
`(1 + δ) N`, while a feasible comparator pays at most `(2N + 2k)/(2k+1) + 1`. -/
theorem exists_input_large (algorithm : ThresholdAlgorithm Page)
    (online : algorithm.Online)
    {k : ℕ} (hk : 1 ≤ k) (pages : Fin (k + 2) ↪ Page) {N : ℕ} (hN : 1 ≤ N) :
    ∃ (input : Instance Page) (comparator : Schedule Page),
      input.cacheSize = k ∧
      input.pageUniverse.card ≤ k + 2 ∧
      comparator.Feasible input ∧
      (1 + algorithm.threshold k) * N ≤ (algorithm.run input).totalCost input ∧
      (2 * k + 1 : Cost) * comparator.totalCost input ≤ 2 * N + 2 * k + (2 * k + 1) := by
  set c : Cost := algorithm.threshold k + 1 with hcdef
  have hc : 0 < c := by positivity
  obtain ⟨input, comparator, window, hsize, hcard, hlength, hfeasible, hdelay, hmisses,
    hpenalty, hordered, hcost⟩ :=
    DeadlineLowerBound.exists_input_charged
      (scaledAlgorithm_online online c hc) hk pages hN
  set scaled := scaleInstance c hc input with hscaled
  have hscaledSize : scaled.cacheSize = k := hsize
  -- the comparator pays no delay, so scaling does not change its cost
  have hzero : ∀ (inp : Instance Page), (∀ r ∈ inp.requests, comparator.requestCost r = 0) →
      comparator.totalDelay inp = 0 := by
    intro inp h
    exact List.sum_eq_zero fun x hx => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact h r hr
  have hscaledDelay : ∀ r ∈ scaled.requests, comparator.requestCost r = 0 := by
    intro r hr
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hr
    rw [requestCost_scale, hdelay original horiginal, mul_zero]
  have hcompCost : comparator.totalCost scaled = comparator.totalCost input := by
    simp only [Schedule.totalCost, hzero _ hdelay, hzero _ hscaledDelay]
  -- the threshold algorithm pays `1 + δ` for every request
  have halg := cost_ge algorithm scaled
    (fun r => window (scaleRequest c⁻¹ (inv_pos.mpr hc) r))
    (by
      intro r hr
      obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hr
      exact hmisses original horiginal)
    (by
      intro r hr wait hwait
      obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hr
      simp only [scaleRequest_inv] at hwait
      rw [hscaledSize]
      show algorithm.threshold k < c * original.delay wait
      calc algorithm.threshold k < c := by rw [hcdef]; exact lt_add_one _
        _ = c * 1 := (mul_one c).symm
        _ ≤ c * original.delay wait := mul_le_mul_right
            ((hpenalty original horiginal).trans (original.delay_mono hwait.le)) c)
    (by
      refine List.pairwise_map.mpr (hordered.imp ?_)
      intro first second h
      simpa only [scaleRequest_inv] using h)
  rw [hscaledSize] at halg
  refine ⟨scaled, comparator, hscaledSize, (pageUniverse_scale c hc input).symm ▸ hcard,
    (feasible_scale_iff _ c hc input).mpr hfeasible, ?_, hcompCost ▸ hcost⟩
  have hlen : scaled.requests.length = N := by
    rw [hscaled, scaleInstance, List.length_map, hlength]
  rw [hlen] at halg
  exact halg

end ThresholdLowerBound

end
end PagingWithDelay
