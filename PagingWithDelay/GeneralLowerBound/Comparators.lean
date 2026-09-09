import PagingWithDelay.GeneralLowerBound.Averaging
import PagingWithDelay.GeneralLowerBound.Dynamic
import PagingWithDelay.GeneralLowerBound.Static

/-!
# All `2k+1` offline comparators

Combine the `k+1` static schedules and the `k` dynamic schedules on the same
input. The bound here depends only on the request count and the delay from
holding every request until the terminal time. The adaptive part of the lower
bound must compare these two quantities with the online algorithm's cost.
-/

namespace PagingWithDelay.GeneralLowerBound

open scoped BigOperators

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- Concrete feasible witnesses for the entire averaging family. -/
theorem exists_comparisonFamily (input : Instance Page) (valid : input.Valid)
    (pages : Finset Page) (hcard : pages.card = input.cacheSize + 1)
    (hstrict : input.requests.Pairwise (fun a b => a.arrival < b.arrival))
    (terminal : Time)
    (hrequests : ∀ r ∈ input.requests, r.page ∈ pages ∧ 0 < r.arrival ∧ r.arrival ≤ terminal) :
    ∃ family : ComparisonFamily Page (2 * input.cacheSize + 1),
      family.input = input ∧
      (∑ i, (family.comparator i).totalCost input) ≤
        (input.cacheSize : Cost) * input.cacheSize + (pages.card : Cost) * pages.card +
          input.requests.length +
          (input.requests.map (fun r => r.delay (terminal - r.arrival))).sum := by
  obtain ⟨dynamic, hfeasible, _, _, hcost⟩ :=
    exists_dynamic_comparators input pages hcard hstrict
      (fun r hr => ⟨(hrequests r hr).1, (hrequests r hr).2.1⟩)
  let index : Fin (2 * input.cacheSize + 1) ≃ (↥pages ⊕ Fin input.cacheSize) :=
    Fintype.equivOfCardEq (by simp [hcard]; omega)
  let comparator : (↥pages ⊕ Fin input.cacheSize) → Schedule Page :=
    Sum.elim (fun hole => staticComparator pages hole terminal) dynamic
  refine ⟨⟨input, valid, fun i => comparator (index i), ?_⟩, rfl, ?_⟩
  · intro i
    cases hi : index i with
    | inl hole =>
        simpa [hi, comparator] using
          staticComparator_feasible input valid pages hole hole.property hcard terminal hrequests
    | inr j => simpa [hi, comparator] using hfeasible j
  · change (∑ i, (comparator (index i)).totalCost input) ≤ _
    rw [index.sum_comp (fun i => (comparator i).totalCost input), Fintype.sum_sum_type]
    have hstatic := sum_staticComparator_cost_le input pages terminal hrequests
    have hs : (∑ i : ↥pages, (staticComparator pages i terminal).totalCost input) ≤
        (pages.card : Cost) * pages.card +
          (input.requests.map (fun r => r.delay (terminal - r.arrival))).sum := by
      rw [Finset.sum_coe_sort pages (fun hole =>
        (staticComparator pages hole terminal).totalCost input)]
      exact hstatic
    calc
      _ ≤ ((pages.card : Cost) * pages.card +
          (input.requests.map (fun r => r.delay (terminal - r.arrival))).sum) +
          ((input.cacheSize : Cost) * input.cacheSize + input.requests.length) :=
        add_le_add hs hcost
      _ = _ := by ring

/-- Once the adaptive input forces one fetch per request and controls terminal
delay, the comparator construction gives exactly the aggregate estimate needed
by averaging. The estimate concerns this same input and this same schedule. -/
theorem exists_comparisonFamily_of_delay_bound (input : Instance Page) (valid : input.Valid)
    (pages : Finset Page) (hcard : pages.card = input.cacheSize + 1)
    (hstrict : input.requests.Pairwise (fun a b => a.arrival < b.arrival))
    (terminal : Time)
    (hrequests : ∀ r ∈ input.requests, r.page ∈ pages ∧ 0 < r.arrival ∧ r.arrival ≤ terminal)
    (schedule : Schedule Page) (ε overhead : Cost)
    (hfetch : input.requests.length ≤ schedule.fetchCount)
    (hdelay : (input.requests.map (fun r => r.delay (terminal - r.arrival))).sum ≤
      (1 + ε) * schedule.totalDelay input + overhead) :
    ∃ family : ComparisonFamily Page (2 * input.cacheSize + 1),
      family.input = input ∧
      (∑ i, (family.comparator i).totalCost input) ≤
        (1 + ε) * schedule.totalCost input +
          ((input.cacheSize : Cost) * input.cacheSize +
            (pages.card : Cost) * pages.card + overhead) := by
  obtain ⟨family, hinput, hcost⟩ :=
    exists_comparisonFamily input valid pages hcard hstrict terminal hrequests
  refine ⟨family, hinput, hcost.trans ?_⟩
  have hn : (input.requests.length : Cost) ≤ (1 + ε) * schedule.fetchCount :=
    (Nat.cast_le.mpr hfetch).trans
      (le_mul_of_one_le_left (zero_le _) (le_add_of_nonneg_right (zero_le ε)))
  calc
    _ ≤ (input.cacheSize : Cost) * input.cacheSize + (pages.card : Cost) * pages.card +
        (1 + ε) * schedule.fetchCount + ((1 + ε) * schedule.totalDelay input + overhead) := by
      gcongr
    _ = _ := by unfold Schedule.totalCost; ring

end
end PagingWithDelay.GeneralLowerBound
