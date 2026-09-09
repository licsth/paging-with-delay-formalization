import PagingWithDelay.Competitive.Ticks
import PagingWithDelay.Competitive.FIFOEviction

/-! Proof-local data extracted from the class-C branch. -/

namespace PagingWithDelay.Competitive

open Set
variable {Page : Type*} [DecidableEq Page]
noncomputable section

/-- Classical decidability, needed to elaborate the `decide`/`filter` forms
below.  It leaves no trace in the proof terms. -/
local instance classCDataPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private theorem previousTime_exists_of_previousIndex (input : Instance Page)
    (i : PaymentIndex input) {p : ℕ} (hp : previousIndex? input i = some p) :
    ∃ time, previousTime? input i = some time := by
  have hmem : p ∈ previousCandidates input i := by
    unfold previousIndex? at hp
    split at hp
    · injection hp with heq
      subst p
      exact Finset.max'_mem _ (by assumption)
    · simp at hp
  have hpi : p < i := Finset.mem_range.mp (Finset.mem_filter.mp hmem).1
  have hplen : p < (fifoRun input).payments.length := hpi.trans i.isLt
  refine ⟨((fifoRun input).payments[p]'hplen).time, ?_⟩
  simp [previousTime?, hp, List.getElem?_eq_getElem hplen]

private theorem previousIndex_exists_of_previousTime (input : Instance Page)
    (i : PaymentIndex input) {time : Time} (ht : previousTime? input i = some time) :
    ∃ p, previousIndex? input i = some p := by
  unfold previousTime? at ht
  cases hp : previousIndex? input i with
  | none =>
      rw [hp] at ht
      contradiction
  | some p => exact ⟨p, rfl⟩

private theorem relevant_data (input : Instance Page) (comparator : Schedule Page)
    (i : PaymentIndex input) {interval : ResidencyInterval (Page := Page)}
    (hinterval : interval ∈ relevantResidencies input comparator i) :
    interval ∈ residencies comparator ∧
      interval.page = (payment input i).page ∧
      ∃ t, t ∈ paymentWindow input i ∧ interval.ContainsBefore t := by
  exact ⟨(List.mem_filter.mp hinterval).1,
    of_decide_eq_true (List.mem_filter.mp hinterval).2⟩

private theorem residency_is_fetch (comparator : Schedule Page)
    {interval : ResidencyInterval (Page := Page)}
    (hinterval : interval ∈ residencies comparator) :
    ∃ event ∈ comparator.events,
      event.fetched = interval.page ∧ event.time = interval.start := by
  obtain ⟨n, hn⟩ := List.mem_iff_get.mp hinterval
  let index : Fin comparator.events.length :=
    ⟨n, by simpa [residencies] using n.isLt⟩
  have heq : residencyAt comparator index = interval := by
    simpa [residencies, index] using hn
  refine ⟨comparator.events.get index, List.get_mem _ _, ?_, ?_⟩
  · simpa [residencyAt] using congrArg ResidencyInterval.page heq
  · simpa [residencyAt] using congrArg ResidencyInterval.start heq

/-- The fallback `previousTime? = none` in the syntactic class-C branch is
unreachable: a relevant residency would begin with a comparator fetch inside
the initial payment window, making the payment class A. -/
theorem classC_previousTime_exists (input : Instance Page)
    (comparator : Schedule Page) (i : PaymentIndex input)
    (hclass : paymentClass input comparator i = .C) :
    ∃ previous, previousTime? input i = some previous := by
  unfold paymentClass at hclass
  split at hclass
  · simp at hclass
  split at hclass
  · simp at hclass
  rename_i hnotA hnotD
  cases hr : relevantResidencies input comparator i with
  | nil => exact (hnotD ⟨hnotA, hr⟩).elim
  | cons interval rest =>
      cases hp : previousTime? input i with
      | some previous => exact ⟨previous, rfl⟩
      | none =>
          exfalso
          have hrel : interval ∈ relevantResidencies input comparator i := by simp [hr]
          obtain ⟨hres, hpage, t, htWindow, htContains⟩ :=
            relevant_data input comparator i hrel
          obtain ⟨event, hevent, heventPage, heventStart⟩ :=
            residency_is_fetch comparator hres
          apply hnotA
          refine ⟨event, hevent, heventPage.trans hpage, ?_⟩
          unfold paymentWindow at htWindow
          have hpIndex : previousIndex? input i = none := by
            cases hx : previousIndex? input i with
            | none => rfl
            | some p =>
                obtain ⟨time, htime⟩ := previousTime_exists_of_previousIndex input i hx
                rw [hp] at htime
                contradiction
          rw [hpIndex] at htWindow
          rw [heventStart]
          change t ∈ Icc 0 (paymentTime input i) at htWindow
          rw [paymentWindow, hpIndex]
          change interval.start ∈ Icc 0 (paymentTime input i)
          exact ⟨bot_le, htContains.1.le.trans htWindow.2⟩

/-- Concrete branch data supplied by a genuine class-C payment. -/
theorem classC_branch_data (input : Instance Page) (comparator : Schedule Page)
    (i : PaymentIndex input) (hclass : paymentClass input comparator i = .C) :
    ¬ IsClassA input comparator i ∧
      ∃ previous interval rest,
        previousTime? input i = some previous ∧
        relevantResidencies input comparator i = interval :: rest ∧
        interval.start ≤ previous := by
  obtain ⟨previous, hp⟩ := classC_previousTime_exists input comparator i hclass
  unfold paymentClass at hclass
  split at hclass
  · simp at hclass
  split at hclass
  · simp at hclass
  rename_i hnotA hnotD
  refine ⟨hnotA, ?_⟩
  cases hr : relevantResidencies input comparator i with
  | nil => exact (hnotD ⟨hnotA, hr⟩).elim
  | cons interval rest =>
      refine ⟨previous, interval, rest, hp, rfl, ?_⟩
      simp [hp, hr] at hclass
      exact hclass

/-- The relevant class-C residency extends past the FIFO eviction time. -/
theorem classC_residency_beyond_eviction (input : Instance Page)
    (comparator : Schedule Page) (i : PaymentIndex input)
    (hclass : paymentClass input comparator i = .C) :
    ∃ previous interval rest eviction,
      previousTime? input i = some previous ∧
      relevantResidencies input comparator i = interval :: rest ∧
      evictionTime? input i = some eviction ∧
      interval.start ≤ previous ∧
      interval.finish.elim True (eviction < ·) := by
  obtain ⟨hnotA, previous, interval, rest, hp, hr, hstart⟩ :=
    classC_branch_data input comparator i hclass
  have hrel : interval ∈ relevantResidencies input comparator i := by simp [hr]
  obtain ⟨_, _, t, htWindow, htContains⟩ := relevant_data input comparator i hrel
  cases he : evictionTime? input i with
  | none =>
      unfold paymentWindow at htWindow
      have hpIndex := previousIndex_exists_of_previousTime input i hp
      obtain ⟨p, hpIndex⟩ := hpIndex
      simp [hpIndex, he] at htWindow
  | some eviction =>
      refine ⟨previous, interval, rest, eviction, hp, hr, rfl, hstart, ?_⟩
      unfold paymentWindow at htWindow
      have hpIndex := previousIndex_exists_of_previousTime input i hp
      obtain ⟨p, hpIndex⟩ := hpIndex
      rw [hpIndex, he] at htWindow
      change t ∈ Ioc eviction (paymentTime input i) at htWindow
      unfold ResidencyInterval.ContainsBefore at htContains
      cases hf : interval.finish with
      | none =>
          change True
          trivial
      | some finish =>
          simp only [hf, Option.elim_some] at htContains ⊢
          exact htWindow.1.trans_le htContains.2

theorem classC_evictionIndex_exists (input : Instance Page)
    (comparator : Schedule Page) (i : PaymentIndex input)
    (hclass : paymentClass input comparator i = .C) :
    ∃ eviction, evictionIndex? input i = some eviction := by
  obtain ⟨_, _, _, eviction, _, _, he, _, _⟩ :=
    classC_residency_beyond_eviction input comparator i hclass
  unfold evictionTime? at he
  cases hi : evictionIndex? input i with
  | none =>
      rw [hi] at he
      contradiction
  | some eviction => exact ⟨eviction, rfl⟩

private theorem previousIndex_lt (input : Instance Page) (i : PaymentIndex input)
    {p : ℕ} (hp : previousIndex? input i = some p) : p < i := by
  have hm : p ∈ previousCandidates input i := by
    unfold previousIndex? at hp
    split at hp
    · injection hp with h; subst p
      exact Finset.max'_mem _ (by assumption)
    · simp at hp
  exact Finset.mem_range.mp (Finset.mem_filter.mp hm).1

private theorem evictionIndex_lt (input : Instance Page) (i : PaymentIndex input)
    {p e : ℕ} (hp : previousIndex? input i = some p)
    (he : evictionIndex? input i = some e) : e < i := by
  unfold evictionIndex? at he
  rw [hp] at he
  exact List.mem_range.mp (List.mem_of_find?_eq_some he)

/-- Fully typed data needed to construct the paper's `Theta_i`. -/
theorem classC_index_residency_data (input : Instance Page) (valid : input.Valid)
    (comparator : Schedule Page) (i : PaymentIndex input)
    (hclass : paymentClass input comparator i = .C) :
    ∃ (previous eviction : PaymentIndex input)
      (interval : ResidencyInterval (Page := Page)),
      previousIndex? input i = some previous ∧
      evictionIndex? input i = some eviction ∧
      (previous : ℕ) + input.cacheSize ≤ (eviction : ℕ) ∧
      interval ∈ residencies comparator ∧
      interval.page = (payment input i).page ∧
      interval.start ≤ paymentTime input previous ∧
      interval.finish.elim True (paymentTime input eviction < ·) := by
  obtain ⟨previousTime, interval, rest, evictionTime,
      hpTime, hr, heTime, hstart, hfinish⟩ :=
    classC_residency_beyond_eviction input comparator i hclass
  obtain ⟨p, hp⟩ := previousIndex_exists_of_previousTime input i hpTime
  obtain ⟨e, he⟩ := classC_evictionIndex_exists input comparator i hclass
  have hpLt := previousIndex_lt input i hp
  have heLt := evictionIndex_lt input i hp he
  let pIndex : PaymentIndex input := ⟨p, hpLt.trans i.isLt⟩
  let eIndex : PaymentIndex input := ⟨e, heLt.trans i.isLt⟩
  have hpTimeEq : previousTime = paymentTime input pIndex := by
    have hlen : p < (fifoRun input).payments.length := hpLt.trans i.isLt
    rw [previousTime?, hp] at hpTime
    simp only [Option.bind_some] at hpTime
    rw [List.getElem?_eq_getElem hlen] at hpTime
    exact Option.some.inj hpTime.symm
  have heTimeEq : evictionTime = paymentTime input eIndex := by
    have hlen : e < (fifoRun input).payments.length := heLt.trans i.isLt
    rw [evictionTime?, he] at heTime
    simp only [Option.bind_some] at heTime
    rw [List.getElem?_eq_getElem hlen] at heTime
    exact Option.some.inj heTime.symm
  have hrel : interval ∈ relevantResidencies input comparator i := by simp [hr]
  have hrd := relevant_data input comparator i hrel
  refine ⟨pIndex, eIndex, interval, hp, he, ?_, hrd.1, hrd.2.1, ?_, ?_⟩
  · exact evictionIndex_ge_previous_add_cacheSize input valid i hp he
  · simpa [hpTimeEq] using hstart
  · simpa [heTimeEq] using hfinish

/-- Typed version of `Theta_i`, directly inhabiting the global tick universe. -/
def thetaTicks (input : Instance Page) (page : Page)
    (previous eviction : PaymentIndex input) :
    Finset (Σ _ : PaymentIndex input, Page) :=
  (Finset.Icc previous eviction).image fun j => ⟨j, page⟩

@[simp] theorem thetaTicks_card (input : Instance Page) (page : Page)
    (previous eviction : PaymentIndex input) :
    (thetaTicks input page previous eviction).card =
      (eviction : ℕ) + 1 - (previous : ℕ) := by
  rw [thetaTicks, Finset.card_image_iff.mpr]
  · simp
  · intro a _ b _ h
    exact congrArg Sigma.fst h

end
end PagingWithDelay.Competitive
