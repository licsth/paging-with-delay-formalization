import Model

/-!
# From comparator schedules to comparator algorithms

`Model.lean` measures competitiveness against comparator *algorithms*, while
the proofs produce, instance by instance, a feasible comparator *schedule*.
The two are interchangeable:

* an upper bound against every feasible schedule is one against every
  algorithm, since an algorithm's schedule is feasible
  (`Algorithm.strictlyCompetitive_of_schedules`);
* a comparator schedule on one instance extends to a comparator algorithm that
  answers every other instance as some fixed algorithm does (`Algorithm.patch`),
  so a lower bound against schedules is one against algorithms
  (`Algorithm.not_competitive_of_schedules`), and conversely
  (`Algorithm.StrictlyCompetitive.le_of_feasible`,
  `Algorithm.exists_schedule_of_not_competitive`).

The fixed algorithm can be the algorithm under consideration itself, so none
has to be constructed.  The same holds for deadline algorithms and comparator
schedules meeting every deadline.
-/

namespace PagingWithDelay

noncomputable section

variable {Page : Type*} [DecidableEq Page]

/-! ## Patching an algorithm on one instance -/

open Classical in
/-- `base`, except that it answers `input` with `schedule`. -/
def Algorithm.patch (base : Algorithm Page) (input : Instance Page)
    (schedule : Schedule Page) (feasible : schedule.Feasible input) : Algorithm Page where
  run other := if other = input then schedule else base other
  feasible other := by
    by_cases h : other = input
    · subst h
      simpa using feasible
    · simpa [h] using base.feasible other

@[simp] theorem Algorithm.patch_self (base : Algorithm Page) (input : Instance Page)
    (schedule : Schedule Page) (feasible : schedule.Feasible input) :
    base.patch input schedule feasible input = schedule := by
  simp [Algorithm.patch]

/-- `base`, except that it answers `input` with `schedule`, which meets every
deadline of `input`. -/
def DeadlineAlgorithm.patch (base : DeadlineAlgorithm Page) (input : Instance Page)
    (schedule : Schedule Page) (feasible : schedule.Feasible input)
    (meets : ∀ request ∈ input.requests, schedule.requestCost request = 0) :
    DeadlineAlgorithm Page where
  toAlgorithm := base.toAlgorithm.patch input schedule feasible
  meetsDeadlines other := by
    by_cases h : other = input
    · subst h
      simpa [Algorithm.patch] using meets
    · simpa [Algorithm.patch, h] using base.meetsDeadlines other

@[simp] theorem DeadlineAlgorithm.patch_self (base : DeadlineAlgorithm Page)
    (input : Instance Page) (schedule : Schedule Page) (feasible : schedule.Feasible input)
    (meets : ∀ request ∈ input.requests, schedule.requestCost request = 0) :
    base.patch input schedule feasible meets input = schedule :=
  Algorithm.patch_self base.toAlgorithm input schedule feasible

/-! ## Competitiveness against schedules -/

/-- An upper bound against every feasible comparator schedule is strict
competitiveness. -/
theorem Algorithm.strictlyCompetitive_of_schedules {algorithm : Algorithm Page}
    {ratio : ℕ → Cost} {inputs : Instance Page → Prop}
    (h : ∀ input, inputs input → ∀ comparator : Schedule Page, comparator.Feasible input →
      (algorithm input).totalCost input ≤ ratio input.cacheSize * comparator.totalCost input) :
    algorithm.StrictlyCompetitive ratio inputs :=
  fun comparator input hinput => h input hinput _ (comparator.feasible input)

/-- If every choice of additive constants is beaten by some feasible comparator schedule,
the algorithm is not competitive. -/
theorem Algorithm.not_competitive_of_schedules {algorithm : Algorithm Page}
    {ratio : ℕ → Cost} {inputs : Instance Page → Prop}
    (h : ∀ additive : ℕ → Cost, ∃ (input : Instance Page) (comparator : Schedule Page),
      inputs input ∧ comparator.Feasible input ∧
        ratio input.cacheSize * comparator.totalCost input + additive input.cacheSize <
          (algorithm input).totalCost input) :
    ¬ algorithm.Competitive ratio inputs := by
  rintro ⟨additive, hbound⟩
  obtain ⟨input, comparator, hinput, hfeasible, hcost⟩ := h additive
  have hle := hbound (algorithm.patch input comparator hfeasible) input hinput
  rw [Algorithm.patch_self] at hle
  exact absurd hle (not_le.mpr hcost)

/-- If every choice of additive constants is beaten by some feasible comparator schedule
meeting every deadline, the deadline algorithm is not competitive. -/
theorem DeadlineAlgorithm.not_competitive_of_schedules {algorithm : DeadlineAlgorithm Page}
    {ratio : ℕ → Cost} {inputs : Instance Page → Prop}
    (h : ∀ additive : ℕ → Cost, ∃ (input : Instance Page) (comparator : Schedule Page),
      inputs input ∧ comparator.Feasible input ∧
        (∀ request ∈ input.requests, comparator.requestCost request = 0) ∧
        ratio input.cacheSize * comparator.totalCost input + additive input.cacheSize <
          (algorithm input).totalCost input) :
    ¬ algorithm.Competitive ratio inputs := by
  rintro ⟨additive, hbound⟩
  obtain ⟨input, comparator, hinput, hfeasible, hmeets, hcost⟩ := h additive
  have hle := hbound (algorithm.patch input comparator hfeasible hmeets) input hinput
  rw [DeadlineAlgorithm.patch_self] at hle
  exact absurd hle (not_le.mpr hcost)

/-! ## Back to schedules -/

/-- Strict competitiveness bounds the cost against every feasible comparator
schedule, not only against the schedules of algorithms. -/
theorem Algorithm.StrictlyCompetitive.le_of_feasible {algorithm : Algorithm Page}
    {ratio : ℕ → Cost} {inputs : Instance Page → Prop}
    (competitive : algorithm.StrictlyCompetitive ratio inputs)
    {input : Instance Page} (hinput : inputs input)
    {comparator : Schedule Page} (feasible : comparator.Feasible input) :
    (algorithm input).totalCost input ≤ ratio input.cacheSize * comparator.totalCost input := by
  simpa using competitive (algorithm.patch input comparator feasible) input hinput

/-- A non-competitive algorithm is beaten, for every choice of additive constants, by some
feasible comparator schedule. -/
theorem Algorithm.exists_schedule_of_not_competitive {algorithm : Algorithm Page}
    {ratio : ℕ → Cost} {inputs : Instance Page → Prop}
    (h : ¬ algorithm.Competitive ratio inputs) (additive : ℕ → Cost) :
    ∃ (input : Instance Page) (comparator : Schedule Page),
      inputs input ∧ comparator.Feasible input ∧
        ratio input.cacheSize * comparator.totalCost input + additive input.cacheSize <
          (algorithm input).totalCost input := by
  by_contra hnone
  push_neg at hnone
  exact h ⟨additive, fun comparator input hinput =>
    hnone input (comparator input) hinput (comparator.feasible input)⟩

/-- A non-competitive deadline algorithm is beaten, for every choice of
additive constants, by some feasible comparator schedule meeting every deadline. -/
theorem DeadlineAlgorithm.exists_schedule_of_not_competitive
    {algorithm : DeadlineAlgorithm Page} {ratio : ℕ → Cost} {inputs : Instance Page → Prop}
    (h : ¬ algorithm.Competitive ratio inputs) (additive : ℕ → Cost) :
    ∃ (input : Instance Page) (comparator : Schedule Page),
      inputs input ∧ comparator.Feasible input ∧
        (∀ request ∈ input.requests, comparator.requestCost request = 0) ∧
        ratio input.cacheSize * comparator.totalCost input + additive input.cacheSize <
          (algorithm input).totalCost input := by
  by_contra hnone
  push_neg at hnone
  exact h ⟨additive, fun comparator input hinput =>
    hnone input (comparator input) hinput (comparator.feasible input)
      (comparator.meetsDeadlines input)⟩

end

end PagingWithDelay
