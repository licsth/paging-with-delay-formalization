import PagingWithDelay.Analysis.Averaging
import PagingWithDelay.Model

/-!
# Applying averaging to paging schedules

This module isolates the final reduction in the general lower-bound proof.
The hypothesis is the substantive construction obligation: on arbitrarily
costly inputs, exhibit `2k+1` feasible schedules whose aggregate cost is at
most `(1+ε) ALG` plus a constant independent of input length.

The theorem below is conditional on that obligation; it is not by itself the
general lower bound for arbitrary online algorithms.
-/

namespace PagingWithDelay.GeneralLowerBound

open scoped BigOperators

variable {Page : Type*} [DecidableEq Page]

/-- A legal input together with an indexed family of feasible offline
schedules. Each schedule uses the model's empty initial cache. -/
structure ComparisonFamily (Page : Type*) [DecidableEq Page] (n : ℕ) where
  input : Instance Page
  valid : input.Valid
  comparator : Fin n → Schedule Page
  feasible : ∀ i, (comparator i).Feasible input

/-- The averaging and asymptotic steps of the general lower bound, with all
instance construction and schedule feasibility obligations explicit. -/
theorem competitive_ratio_lower_bound_of_families (algorithm : Algorithm Page)
    (k : ℕ) (pages : Finset Page) (ratio additive : Cost)
    (hratio : ratio < (2 * k + 1 : ℕ))
    (hfamily : ∀ ε : Cost, 0 < ε → ∃ overhead : Cost,
      ∀ bound : Cost, ∃ family : ComparisonFamily Page (2 * k + 1),
        (family.input.cacheSize = k ∧
          ∀ request ∈ family.input.requests, request.page ∈ pages) ∧
        bound < (algorithm family.input family.valid).totalCost family.input ∧
        (∑ i, (family.comparator i).totalCost family.input) ≤
          (1 + ε) * (algorithm family.input family.valid).totalCost family.input + overhead) :
    ∃ (input : Instance Page) (valid : input.Valid) (comparator : Schedule Page),
      input.cacheSize = k ∧
      (∀ request ∈ input.requests, request.page ∈ pages) ∧
      comparator.Feasible input ∧
      ratio * comparator.totalCost input + additive <
        (algorithm input valid).totalCost input := by
  obtain ⟨family, hsize, i, _, hcost⟩ :=
    Analysis.lower_bound_of_approximate_family (Finset.univ : Finset (Fin (2 * k + 1)))
      (fun family : ComparisonFamily Page (2 * k + 1) =>
        (algorithm family.input family.valid).totalCost family.input)
      (fun family i => (family.comparator i).totalCost family.input)
      (fun family => family.input.cacheSize = k ∧
        ∀ request ∈ family.input.requests, request.page ∈ pages)
      ratio additive (by simpa using hratio) hfamily
  exact ⟨family.input, family.valid, family.comparator i, hsize.1, hsize.2,
    family.feasible i, hcost⟩

end PagingWithDelay.GeneralLowerBound
