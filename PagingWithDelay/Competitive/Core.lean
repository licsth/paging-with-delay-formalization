import PagingWithDelay.Competitive.CostDefs
import PagingWithDelay.EventLoop.PaymentOrder

/-!
# Shared definitions for the competitive proof

This file introduces the proof-specific objects from Sections 3.2--3.7 of
`fifo-upper-bound.tex`, together with structural facts shared by the three
per-class charging arguments.
-/

namespace PagingWithDelay

open Set

namespace Competitive

variable {Page : Type*} [DecidableEq Page]

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The completed internal run whose payment log generates FIFO's schedule. -/
def fifoRun (input : Instance Page) : FIFO.State Page :=
  FIFO.run 1 input (2 * input.requests.length) (FIFO.initialState input)

abbrev PaymentIndex (input : Instance Page) := Fin (fifoRun input).payments.length

def payment (input : Instance Page) (i : PaymentIndex input) : FIFO.Payment Page :=
  (fifoRun input).payments.get i

/-- Indices before `i` whose payment fetched the same page. -/
def previousCandidates (input : Instance Page) (i : PaymentIndex input) : Finset ℕ :=
  (Finset.range i).filter fun j =>
    ((fifoRun input).payments[j]?).any fun earlier =>
      earlier.page = (payment input i).page

/-- The index of the preceding payment for the same page, if one exists. -/
def previousIndex? (input : Instance Page) (i : PaymentIndex input) : Option ℕ :=
  if h : (previousCandidates input i).Nonempty then
    some ((previousCandidates input i).max' h)
  else none

/-- The first later payment, before `i`, after which the previously fetched
page is absent. For a valid FIFO run this is its eviction payment. -/
def evictionIndex? (input : Instance Page) (i : PaymentIndex input) : Option ℕ :=
  match previousIndex? input i with
  | none => none
  | some previous =>
      (List.range i).find? fun j =>
        previous < j ∧
        ((fifoRun input).payments[j]?).any fun event =>
          (payment input i).page ∉ event.queueAfter

def paymentTime (input : Instance Page) (i : PaymentIndex input) : Time :=
  (payment input i).time

def previousTime? (input : Instance Page) (i : PaymentIndex input) : Option Time :=
  (previousIndex? input i).bind fun j =>
    ((fifoRun input).payments[j]?).map FIFO.Payment.time

def evictionTime? (input : Instance Page) (i : PaymentIndex input) : Option Time :=
  (evictionIndex? input i).bind fun j =>
    ((fifoRun input).payments[j]?).map FIFO.Payment.time

/-- The payment window `W_i`. The empty fallback exposes a malformed repeated
payment whose intervening eviction has not been established. FIFO invariants
will show that this fallback is unreachable. -/
def paymentWindow (input : Instance Page) (i : PaymentIndex input) : Set Time :=
  match previousIndex? input i, evictionTime? input i with
  | none, _ => Icc 0 (paymentTime input i)
  | some _, some eviction => Ioc eviction (paymentTime input i)
  | some _, none => ∅

/-- The auxiliary interval `I_i`, beginning at the preceding fetch rather than
the eviction. -/
def auxiliaryInterval (input : Instance Page) (i : PaymentIndex input) : Set Time :=
  match previousTime? input i with
  | none => Icc 0 (paymentTime input i)
  | some previous => Ioc previous (paymentTime input i)

private theorem previousCandidate_of_lt_samePage (input : Instance Page)
    {i j : PaymentIndex input} (hlt : (i : ℕ) < j)
    (hpage : (payment input i).page = (payment input j).page) :
    (i : ℕ) ∈ previousCandidates input j := by
  simp only [previousCandidates, Finset.mem_filter, Finset.mem_range]
  refine ⟨hlt, ?_⟩
  rw [List.getElem?_eq_getElem i.isLt]
  simpa [payment] using hpage

private theorem previousIndex?_spec (input : Instance Page) (j : PaymentIndex input)
    {i : ℕ} (hi : i ∈ previousCandidates input j) :
    ∃ previous, previousIndex? input j = some previous ∧
      i ≤ previous ∧ previous ∈ previousCandidates input j := by
  unfold previousIndex?
  split
  · rename_i hnonempty
    exact ⟨_, rfl, Finset.le_max' _ i hi, Finset.max'_mem _ hnonempty⟩
  · rename_i hempty
    exact (hempty ⟨i, hi⟩).elim

theorem paymentTime_mono (input : Instance Page) (valid : input.Valid)
    {i j : PaymentIndex input} (hij : i ≤ j) :
    paymentTime input i ≤ paymentTime input j := by
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  · exact List.pairwise_iff_get.mp
      (FIFO.final_payment_times_chronological input valid) i j hij

theorem auxiliaryInterval_upper (input : Instance Page) (i : PaymentIndex input)
    {t : Time} (ht : t ∈ auxiliaryInterval input i) :
    t ≤ paymentTime input i := by
  unfold auxiliaryInterval at ht
  split at ht <;> exact ht.2

/-- The paper's intervals `I_i` for distinct payments of one page are
disjoint.  This is derived from the definition of the preceding same-page
payment and the chronological FIFO payment log. -/
theorem auxiliaryIntervals_disjoint (input : Instance Page) (valid : input.Valid)
    {i j : PaymentIndex input} (hne : i ≠ j)
    (hpage : (payment input i).page = (payment input j).page) :
    Disjoint (auxiliaryInterval input i) (auxiliaryInterval input j) := by
  wlog hij : (i : ℕ) < j generalizing i j
  · have hji : (j : ℕ) < i := by
      have hnatne : (j : ℕ) ≠ i := by
        intro heq
        apply hne
        exact Fin.ext heq.symm
      omega
    exact (this (i := j) (j := i) (Ne.symm hne) hpage.symm hji).symm
  have hicandidate := previousCandidate_of_lt_samePage input hij hpage
  obtain ⟨previous, hprevious, hip, hpreviousCandidate⟩ :=
    previousIndex?_spec input j hicandidate
  have hpj : previous < (j : ℕ) :=
    Finset.mem_range.mp (Finset.mem_filter.mp hpreviousCandidate).1
  have hplen : previous < (fifoRun input).payments.length := hpj.trans j.isLt
  have hpreviousTime : previousTime? input j =
      some ((fifoRun input).payments[previous]'hplen).time := by
    simp [previousTime?, hprevious, List.getElem?_eq_getElem hplen]
  rw [Set.disjoint_left]
  intro t hti htj
  have htiUpper := auxiliaryInterval_upper input i hti
  have hiPrevious : paymentTime input i ≤
      ((fifoRun input).payments[previous]'hplen).time := by
    let p : PaymentIndex input := ⟨previous, hplen⟩
    exact paymentTime_mono input valid (show i ≤ p from hip)
  unfold auxiliaryInterval at htj
  rw [hpreviousTime] at htj
  exact (not_lt_of_ge (htiUpper.trans hiPrevious)) htj.1

/-- A maximal comparator residency period starts at a fetch and ends at the
first later event after which the fetched page is absent. `none` means that the
page remains resident after the comparator's final event. -/
structure ResidencyInterval where
  page : Page
  start : Time
  finish : Option Time

def firstEvictionAfter (schedule : Schedule Page) (i : Fin schedule.events.length) :
    Option Time :=
  let event := schedule.events.get i
  ((List.range schedule.events.length).find? fun j =>
    (i : ℕ) < j ∧ (schedule.events[j]?).any fun later =>
      event.fetched ∉ later.cacheAfter).bind fun j =>
        (schedule.events[j]?).map FetchEvent.time

def residencyAt (schedule : Schedule Page) (i : Fin schedule.events.length) :
    ResidencyInterval (Page := Page) :=
  let event := schedule.events.get i
  { page := event.fetched
    start := event.time
    finish := firstEvictionAfter schedule i }

def residencies (schedule : Schedule Page) : List (ResidencyInterval (Page := Page)) :=
  List.ofFn fun i : Fin schedule.events.length => residencyAt schedule i

def ResidencyInterval.Contains (interval : ResidencyInterval (Page := Page))
    (t : Time) : Prop :=
  interval.start ≤ t ∧ interval.finish.elim True (t < ·)

/-- Residency as observed immediately before transitions at `t`: a fetch at
`t` is not yet visible, while an eviction at `t` has not happened yet. -/
def ResidencyInterval.ContainsBefore (interval : ResidencyInterval (Page := Page))
    (t : Time) : Prop :=
  interval.start < t ∧ interval.finish.elim True (t ≤ ·)

def relevantResidencies (input : Instance Page) (comparator : Schedule Page)
    (i : PaymentIndex input) : List (ResidencyInterval (Page := Page)) :=
  (residencies comparator).filter fun interval =>
    decide (interval.page = (payment input i).page ∧
      ∃ t, t ∈ paymentWindow input i ∧ interval.ContainsBefore t)

/-- Class A: the comparator fetches the requested page inside `W_i`. -/
def IsClassA (input : Instance Page) (comparator : Schedule Page)
    (i : PaymentIndex input) : Prop :=
  ∃ event ∈ comparator.events,
    event.fetched = (payment input i).page ∧ event.time ∈ paymentWindow input i

/-- Class D: the comparator never has the requested page resident in `W_i`. -/
def IsClassD (input : Instance Page) (comparator : Schedule Page)
    (i : PaymentIndex input) : Prop :=
  ¬ IsClassA input comparator i ∧ relevantResidencies input comparator i = []

/-- The paper's four mutually exclusive cases, selected in priority order.
For the non-A/non-D case, the relevant residency start is compared with the
previous FIFO payment time, yielding B or C. -/
inductive PaymentClass where | A | B | C | D
  deriving DecidableEq

def paymentClass (input : Instance Page) (comparator : Schedule Page)
    (i : PaymentIndex input) : PaymentClass :=
  if IsClassA input comparator i then .A
  else if IsClassD input comparator i then .D
  else
    match previousTime? input i, relevantResidencies input comparator i with
    | some previous, interval :: _ =>
        if previous < interval.start then .B else .C
    | _, _ => .C

def classIndices (category : PaymentClass) (input : Instance Page)
    (comparator : Schedule Page) : Finset (PaymentIndex input) :=
  Finset.univ.filter fun i => paymentClass input comparator i = category

def classCount (category : PaymentClass) (input : Instance Page)
    (comparator : Schedule Page) : ℕ :=
  (classIndices category input comparator).card

set_option maxRecDepth 10000 in
theorem payment_classes_exhaustive (input : Instance Page)
    (comparator : Schedule Page) :
    (fifoRun input).payments.length =
      classCount .A input comparator + classCount .B input comparator +
      classCount .C input comparator + classCount .D input comparator := by
  classical
  simp only [classCount, classIndices]
  have partition : Finset.univ =
      Finset.univ.filter (fun i => paymentClass input comparator i = .A) ∪
      Finset.univ.filter (fun i => paymentClass input comparator i = .B) ∪
      Finset.univ.filter (fun i => paymentClass input comparator i = .C) ∪
      Finset.univ.filter (fun i => paymentClass input comparator i = .D) := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and]
    cases paymentClass input comparator i <;> simp
  have hcard : (fifoRun input).payments.length =
      (Finset.univ : Finset (PaymentIndex input)).card := by
    simp [PaymentIndex]
  calc
    (fifoRun input).payments.length =
        (Finset.univ : Finset (PaymentIndex input)).card := hcard
    _ = (Finset.univ.filter (fun i => paymentClass input comparator i = .A) ∪
        Finset.univ.filter (fun i => paymentClass input comparator i = .B) ∪
        Finset.univ.filter (fun i => paymentClass input comparator i = .C) ∪
        Finset.univ.filter (fun i => paymentClass input comparator i = .D)).card :=
      congrArg Finset.card partition
    _ = _ := by
      rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
        Finset.card_union_of_disjoint]
      · simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ,
          true_and]
        intro i ha hb
        cases ha.symm.trans hb
      · simp only [Finset.disjoint_left, Finset.mem_union, Finset.mem_filter,
          Finset.mem_univ, true_and]
        intro i hab hc
        rcases hab with ha | hb
        · cases ha.symm.trans hc
        · cases hb.symm.trans hc
      · simp only [Finset.disjoint_left, Finset.mem_union, Finset.mem_filter,
          Finset.mem_univ, true_and]
        intro i habc hd
        rcases habc with hab | hc
        · rcases hab with ha | hb
          · cases ha.symm.trans hd
          · cases hb.symm.trans hd
        · cases hc.symm.trans hd

end
end Competitive
end PagingWithDelay
