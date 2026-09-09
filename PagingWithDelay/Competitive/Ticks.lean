import PagingWithDelay.Competitive.ComparatorResidency

/-!
# Finite tick counting for class C

This module contains only the finite combinatorics of the class-C argument.
A tick is a page resident in the comparator cache immediately after all
comparator events at a FIFO payment time.  The class-C proof supplies the
semantic assignment of ticks to payments.
-/

namespace PagingWithDelay.Competitive

variable {Page : Type*} [DecidableEq Page]
noncomputable section

/-- A comparator-residency tick is a payment index paired with a page resident
at that payment time. -/
def comparatorTicks (input : Instance Page) (comparator : Schedule Page) :
    Finset (Σ _ : PaymentIndex input, Page) :=
  Finset.univ.sigma fun i => comparatorCacheAt comparator (paymentTime input i)

@[simp] theorem mem_comparatorTicks (input : Instance Page)
    (comparator : Schedule Page) (i : PaymentIndex input) (page : Page) :
    (⟨i, page⟩ : Σ _ : PaymentIndex input, Page) ∈ comparatorTicks input comparator ↔
      page ∈ comparatorCacheAt comparator (paymentTime input i) := by
  simp [comparatorTicks]

theorem comparatorTicks_card_eq_sum (input : Instance Page)
    (comparator : Schedule Page) :
    (comparatorTicks input comparator).card =
      ∑ i : PaymentIndex input,
        (comparatorCacheAt comparator (paymentTime input i)).card := by
  simp [comparatorTicks]

/-- At most `capacity` pages can tick at each of `paymentCount` indices. -/
theorem comparatorTicks_card_le (input : Instance Page)
    (comparator : Schedule Page) (capacity : ℕ)
    (hcapacity : ∀ i : PaymentIndex input,
      (comparatorCacheAt comparator (paymentTime input i)).card ≤ capacity) :
    (comparatorTicks input comparator).card ≤
      capacity * (fifoRun input).payments.length := by
  rw [comparatorTicks_card_eq_sum]
  calc
    (∑ i : PaymentIndex input,
        (comparatorCacheAt comparator (paymentTime input i)).card) ≤
        ∑ _i : PaymentIndex input, capacity := by
          exact Finset.sum_le_sum fun i _ => hcapacity i
    _ = capacity * (fifoRun input).payments.length := by
      simp [PaymentIndex, Nat.mul_comm]

theorem comparatorTicks_card_le_of_feasible (input : Instance Page)
    (comparator : Schedule Page) (feasible : comparator.Feasible input) :
    (comparatorTicks input comparator).card ≤
      input.cacheSize * (fifoRun input).payments.length := by
  apply comparatorTicks_card_le input comparator input.cacheSize
  intro i
  exact comparatorCacheAt_paymentTime_card_le input comparator feasible _

section Assignment

variable {Source Tick : Type*} [DecidableEq Source] [DecidableEq Tick]

/-- The tagged collection of ticks assigned to sources.  Tags make the
cardinality the sum of the individual assignment cardinalities. -/
def assignedTicks (sources : Finset Source) (assigned : Source → Finset Tick) :
    Finset (Σ _ : Source, Tick) :=
  sources.sigma assigned

omit [DecidableEq Tick] in
/-- Generic counting principle used by class C: if every selected source gets
at least `quota` ticks, all assigned ticks lie in a common universe, and the
assignments of distinct sources are disjoint, then
`quota * numberOfSources ≤ numberOfTicks`. -/
theorem mul_card_le_card_of_disjoint_assignment
    (sources : Finset Source) (tickSet : Finset Tick)
    (assigned : Source → Finset Tick) (quota : ℕ)
    (hquota : ∀ source ∈ sources, quota ≤ (assigned source).card)
    (hsub : ∀ source ∈ sources, assigned source ⊆ tickSet)
    (hdisjoint : ∀ left, left ∈ sources → ∀ right, right ∈ sources →
      left ≠ right → Disjoint (assigned left) (assigned right)) :
    quota * sources.card ≤ tickSet.card := by
  have hsum : quota * sources.card ≤ ∑ source ∈ sources, (assigned source).card := by
    rw [Nat.mul_comm]
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum fun source hsource => hquota source hsource)
  have hcard : (assignedTicks sources assigned).card =
      ∑ source ∈ sources, (assigned source).card := by
    simp [assignedTicks]
  have hmap : Set.MapsTo
      (fun tick : Σ _ : Source, Tick => tick.2)
      (assignedTicks sources assigned : Set (Σ _ : Source, Tick)) tickSet := by
    intro tick htick
    obtain ⟨hsource, hmember⟩ := Finset.mem_sigma.mp htick
    exact hsub tick.1 hsource hmember
  have hinj : Set.InjOn
      (fun tick : Σ _ : Source, Tick => tick.2)
      (assignedTicks sources assigned : Set (Σ _ : Source, Tick)) := by
    intro left hleft right hright heq
    obtain ⟨hleftSource, hleftTick⟩ := Finset.mem_sigma.mp hleft
    obtain ⟨hrightSource, hrightTick⟩ := Finset.mem_sigma.mp hright
    have hsources : left.1 = right.1 := by
      by_contra hne
      have hd := hdisjoint left.1 hleftSource right.1 hrightSource hne
      rw [Finset.disjoint_left] at hd
      have heq' : left.2 = right.2 := heq
      have hrightTick' : left.2 ∈ assigned right.1 := by
        rw [heq']
        exact hrightTick
      exact hd hleftTick hrightTick'
    cases left with
    | mk leftSource leftTick =>
      cases right with
      | mk rightSource rightTick =>
        simp only at hsources heq ⊢
        subst rightSource
        subst rightTick
        rfl
  exact hsum.trans (hcard.symm.le.trans
    (Finset.card_le_card_of_injOn _ hmap hinj))

end Assignment

end
end PagingWithDelay.Competitive
