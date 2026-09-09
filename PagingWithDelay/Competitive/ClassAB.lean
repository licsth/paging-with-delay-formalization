import PagingWithDelay.Competitive.Core

namespace PagingWithDelay.Competitive

open Set

variable {Page : Type*} [DecidableEq Page]
noncomputable section

local instance classABPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private theorem previousIndex_mem (input : Instance Page) (i : PaymentIndex input)
    {previous : ℕ} (h : previousIndex? input i = some previous) :
    previous ∈ previousCandidates input i := by
  unfold previousIndex? at h
  split at h
  · injection h with h
    subst previous
    exact Finset.max'_mem _ (by assumption)
  · simp at h

private theorem evictionIndex_spec (input : Instance Page) (i : PaymentIndex input)
    {previous eviction : ℕ} (hp : previousIndex? input i = some previous)
    (he : evictionIndex? input i = some eviction) :
    previous < eviction ∧ eviction < i := by
  unfold evictionIndex? at he
  rw [hp] at he
  have hmem := List.mem_of_find?_eq_some he
  have htest := List.find?_some he
  have htest' := of_decide_eq_true htest
  constructor
  · exact htest'.1
  · simpa using hmem

private theorem paymentWindow_subset_auxiliary (input : Instance Page)
    (valid : input.Valid) (i : PaymentIndex input) :
    paymentWindow input i ⊆ auxiliaryInterval input i := by
  intro t ht
  unfold paymentWindow at ht
  cases hp : previousIndex? input i with
  | none => simpa [auxiliaryInterval, previousTime?, hp] using ht
  | some previous =>
      cases heIndex : evictionIndex? input i with
      | none => simp [evictionTime?, heIndex, hp] at ht
      | some eviction =>
          have hpMem := previousIndex_mem input i hp
          have hpLtI : previous < i :=
            Finset.mem_range.mp (Finset.mem_filter.mp hpMem).1
          have hpLen : previous < (fifoRun input).payments.length := hpLtI.trans i.isLt
          have hprevTime : previousTime? input i =
              some ((fifoRun input).payments[previous]'hpLen).time := by
            simp [previousTime?, hp, List.getElem?_eq_getElem hpLen]
          have heSpec := evictionIndex_spec input i hp heIndex
          have heLen : eviction < (fifoRun input).payments.length :=
            heSpec.2.trans i.isLt
          have htimes : ((fifoRun input).payments[previous]'hpLen).time ≤
              ((fifoRun input).payments[eviction]'heLen).time := by
            let p : PaymentIndex input := ⟨previous, hpLen⟩
            let e : PaymentIndex input := ⟨eviction, heLen⟩
            exact paymentTime_mono input valid (show p ≤ e from heSpec.1.le)
          simp [evictionTime?, heIndex, List.getElem?_eq_getElem heLen, hp] at ht
          rw [auxiliaryInterval, hprevTime]
          exact ⟨htimes.trans_lt ht.1, ht.2⟩

private theorem classA_iff (input : Instance Page) (comparator : Schedule Page)
    (i : PaymentIndex input) :
    paymentClass input comparator i = .A ↔ IsClassA input comparator i := by
  by_cases hA : IsClassA input comparator i
  · simp [paymentClass, hA]
  · constructor
    · intro himpossible
      unfold paymentClass at himpossible
      rw [if_neg hA] at himpossible
      split at himpossible
      · cases himpossible
      · split at himpossible <;> try cases himpossible
        split at himpossible <;> cases himpossible
    · exact fun h => (hA h).elim

private theorem classB_data (input : Instance Page) (comparator : Schedule Page)
    (i : PaymentIndex input) (hclass : paymentClass input comparator i = .B) :
    ¬ IsClassA input comparator i ∧
      ∃ previous interval rest,
        previousTime? input i = some previous ∧
        relevantResidencies input comparator i = interval :: rest ∧
        previous < interval.start := by
  unfold paymentClass at hclass
  split at hclass
  · simp at hclass
  split at hclass
  · simp at hclass
  rename_i hnotA hnotD
  refine ⟨hnotA, ?_⟩
  cases hp : previousTime? input i with
  | none =>
      cases hr : relevantResidencies input comparator i <;> simp [hp, hr] at hclass
  | some previous =>
      cases hr : relevantResidencies input comparator i with
      | nil => simp [hp, hr] at hclass
      | cons interval rest =>
          refine ⟨previous, interval, rest, ?_⟩
          simp [hp, hr] at hclass
          exact ⟨rfl, rfl, hclass⟩

/-- Every A or B payment has a comparator fetch of its page inside `I_i`. -/
private theorem chargedFetch_exists (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page) (i : PaymentIndex input)
    (hclass : paymentClass input comparator i = .A ∨
      paymentClass input comparator i = .B) :
    ∃ eventIndex : Fin comparator.events.length,
      (comparator.events.get eventIndex).fetched = (payment input i).page ∧
      (comparator.events.get eventIndex).time ∈ auxiliaryInterval input i := by
  rcases hclass with hA | hB
  · obtain ⟨event, hevent, hpage, hwindow⟩ :=
      (classA_iff input comparator i).mp hA
    obtain ⟨eventIndex, hget⟩ := List.mem_iff_get.mp hevent
    refine ⟨eventIndex, ?_, ?_⟩
    · rw [hget]
      exact hpage
    · rw [hget]
      exact paymentWindow_subset_auxiliary input valid i hwindow
  · obtain ⟨hnotA, previous, interval, rest, hp, hr, hstart⟩ :=
      classB_data input comparator i hB
    have hinterval : interval ∈ residencies comparator := by
      have : interval ∈ relevantResidencies input comparator i := by simp [hr]
      exact (List.mem_filter.mp this).1
    obtain ⟨eventIndex, hresidency⟩ := List.mem_iff_get.mp hinterval
    have hfiltered : interval.page = (payment input i).page ∧
        ∃ t, t ∈ paymentWindow input i ∧ interval.ContainsBefore t := by
      have : interval ∈ relevantResidencies input comparator i := by simp [hr]
      exact of_decide_eq_true (List.mem_filter.mp this).2
    let fetchIndex : Fin comparator.events.length :=
      ⟨eventIndex, by simpa [residencies] using eventIndex.isLt⟩
    have hresidency' : residencyAt comparator fetchIndex = interval := by
      simpa [residencies, fetchIndex] using hresidency
    refine ⟨fetchIndex, ?_, ?_⟩
    · have hpageEq := congrArg ResidencyInterval.page hresidency'
      simpa [fetchIndex, residencyAt] using hpageEq.trans hfiltered.1
    · rw [auxiliaryInterval, hp]
      have hstartEq : (comparator.events.get fetchIndex).time = interval.start := by
        simpa [fetchIndex, residencyAt] using
          congrArg ResidencyInterval.start hresidency'
      refine ⟨by rw [hstartEq]; exact hstart, ?_⟩
      obtain ⟨t, htWindow, htInterval⟩ := hfiltered.2
      have hstartLeT : interval.start ≤ t := le_of_lt htInterval.1
      rw [hstartEq]
      exact hstartLeT.trans (auxiliaryInterval_upper input i
        (paymentWindow_subset_auxiliary input valid i htWindow))

private def chargeIndex (input : Instance Page) (comparator : Schedule Page)
    (x : (classIndices .A input comparator) ⊕
      (classIndices .B input comparator)) :
    PaymentIndex input := match x with | .inl i => i | .inr i => i

private theorem chargeIndex_class (input : Instance Page) (comparator : Schedule Page)
    (x : (classIndices .A input comparator) ⊕
      (classIndices .B input comparator)) :
    paymentClass input comparator (chargeIndex input comparator x) = .A ∨
      paymentClass input comparator (chargeIndex input comparator x) = .B := by
  cases x with
  | inl i => exact Or.inl (Finset.mem_filter.mp i.2).2
  | inr i => exact Or.inr (Finset.mem_filter.mp i.2).2

private def chargedFetch (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page)
    (x : (classIndices .A input comparator) ⊕
      (classIndices .B input comparator)) :
    Fin comparator.events.length :=
  Classical.choose (chargedFetch_exists input valid comparator
    (chargeIndex input comparator x) (chargeIndex_class input comparator x))

private theorem chargedFetch_spec (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page)
    (x : (classIndices .A input comparator) ⊕
      (classIndices .B input comparator)) :
    (comparator.events.get (chargedFetch input valid comparator x)).fetched =
        (payment input (chargeIndex input comparator x)).page ∧
      (comparator.events.get (chargedFetch input valid comparator x)).time ∈
        auxiliaryInterval input (chargeIndex input comparator x) := by
  exact Classical.choose_spec (chargedFetch_exists input valid comparator
    (chargeIndex input comparator x) (chargeIndex_class input comparator x))

/-- Classes A and B inject into comparator fetches. -/
theorem classA_classB_bound (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page) (_feasible : comparator.Feasible input) :
    classCount .A input comparator + classCount .B input comparator ≤
      comparator.fetchCount := by
  let Domain := (classIndices .A input comparator) ⊕
    (classIndices .B input comparator)
  have hinjective : Function.Injective (chargedFetch input valid comparator) := by
    intro x y heq
    have spec (z : Domain) := chargedFetch_spec input valid comparator z
    have hevent : comparator.events.get (chargedFetch input valid comparator x) =
        comparator.events.get (chargedFetch input valid comparator y) := by rw [heq]
    have hpage := (spec x).1.symm.trans
      ((congrArg FetchEvent.fetched hevent).trans (spec y).1)
    have hindex : chargeIndex input comparator x =
        chargeIndex input comparator y := by
      by_contra hne
      exact Set.disjoint_left.mp
        (auxiliaryIntervals_disjoint input valid hne hpage)
        ((spec x).2) (by rw [heq]; exact (spec y).2)
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext hindex)
      | inr y =>
        exfalso
        have hA : paymentClass input comparator x = .A :=
          (Finset.mem_filter.mp x.2).2
        have hB : paymentClass input comparator y = .B :=
          (Finset.mem_filter.mp y.2).2
        have hv : (x : PaymentIndex input) = y := by
          simpa [chargeIndex] using hindex
        rw [hv] at hA
        cases hA.symm.trans hB
    | inr x =>
      cases y with
      | inl y =>
        exfalso
        have hB : paymentClass input comparator x = .B :=
          (Finset.mem_filter.mp x.2).2
        have hA : paymentClass input comparator y = .A :=
          (Finset.mem_filter.mp y.2).2
        have hv : (x : PaymentIndex input) = y := by
          simpa [chargeIndex] using hindex
        rw [hv] at hB
        cases hB.symm.trans hA
      | inr y => exact congrArg Sum.inr (Subtype.ext hindex)
  calc
    classCount .A input comparator + classCount .B input comparator =
        Fintype.card Domain := by
          simp [Domain, classCount, Fintype.card_coe]
    _ ≤ Fintype.card (Fin comparator.events.length) :=
      Fintype.card_le_of_injective _ hinjective
    _ = comparator.fetchCount := by simp [Schedule.fetchCount]

end
end PagingWithDelay.Competitive
