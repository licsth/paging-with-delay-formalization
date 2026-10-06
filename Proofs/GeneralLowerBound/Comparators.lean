import Proofs.GeneralLowerBound.Averaging
import Proofs.GeneralLowerBound.Dynamic
import Proofs.GeneralLowerBound.Static

/-!
# All `2k+1` offline comparators

Combine the `k+1` static schedules and the `k` dynamic schedules on the same
input. Their aggregate cost depends only on the request count and the delay
from holding every request until the terminal time; the adaptive input of
`Phases.lean` compares both with the online algorithm's cost.
-/

namespace PagingWithDelay.GeneralLowerBound

open scoped BigOperators

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- Once the adaptive input forces one fetch per request and controls terminal
delay, the `k+1` static and `k` dynamic comparators give exactly the aggregate
estimate needed by averaging. -/
theorem exists_comparisonFamily_of_delay_bound {k : ℕ} (input : Instance Page)
    (hsize : input.cacheSize = k) (pages : Finset Page) (hcard : pages.card = k + 1)
    (hstrict : input.requests.Pairwise (fun a b => a.arrival < b.arrival))
    (terminal : Time)
    (hrequests : ∀ r ∈ input.requests, r.page ∈ pages ∧ 0 < r.arrival ∧ r.arrival ≤ terminal)
    (schedule : Schedule Page) (ε overhead : Cost)
    (hfetch : input.requests.length ≤ schedule.fetchCount)
    (hdelay : (input.requests.map (fun r => r.delay (terminal - r.arrival))).sum ≤
      (1 + ε) * schedule.totalDelay input + overhead) :
    ∃ family : ComparisonFamily Page (2 * k + 1),
      family.input = input ∧
      (∑ i, (family.comparator i).totalCost input) ≤
        (1 + ε) * schedule.totalCost input +
          ((k : Cost) * k + ((k : Cost) + 1) * ((k : Cost) + 1) + overhead) := by
  subst hsize
  obtain ⟨dynamic, hfeasible, hdynamic⟩ :=
    exists_dynamic_comparators input pages hcard hstrict
      (fun r hr => ⟨(hrequests r hr).1, (hrequests r hr).2.1⟩)
  have hstatic := sum_staticComparator_cost_le input pages hcard terminal hrequests
  rw [← Finset.sum_coe_sort] at hstatic
  let index : Fin (2 * input.cacheSize + 1) ≃ (↥pages ⊕ Fin input.cacheSize) :=
    Fintype.equivOfCardEq (by simp [hcard]; omega)
  let comparator : (↥pages ⊕ Fin input.cacheSize) → Schedule Page :=
    Sum.elim (fun hole => staticComparator input.initialCache.toFinset pages hole terminal)
      dynamic
  refine ⟨⟨input, fun i => comparator (index i), fun i => ?_⟩, rfl, ?_⟩
  · show (comparator (index i)).Feasible input
    rcases index i with hole | j
    exacts [staticComparator_feasible input pages hole hole.property hcard terminal hrequests,
      hfeasible j]
  · have hn : (input.requests.length : Cost) ≤ (1 + ε) * schedule.fetchCount :=
      (Nat.cast_le.mpr hfetch).trans (le_mul_of_one_le_left (zero_le _) le_self_add)
    change (∑ i, (comparator (index i)).totalCost input) ≤ _
    rw [index.sum_comp (fun i => (comparator i).totalCost input), Fintype.sum_sum_type]
    calc _ ≤ ((pages.card : Cost) * pages.card +
          (input.requests.map (fun r => r.delay (terminal - r.arrival))).sum) +
          ((input.cacheSize : Cost) * input.cacheSize + input.requests.length) :=
        add_le_add hstatic hdynamic
      _ ≤ (pages.card : Cost) * pages.card + ((1 + ε) * schedule.totalDelay input + overhead) +
          ((input.cacheSize : Cost) * input.cacheSize + (1 + ε) * schedule.fetchCount) := by
        gcongr
      _ = _ := by rw [hcard, Schedule.totalCost]; push_cast; ring

end
end PagingWithDelay.GeneralLowerBound
