import PagingWithDelay.Competitive.ComparatorResidency

/-!
# Comparator semantics used by the class-D charge
-/

namespace PagingWithDelay.Competitive

open Set

variable {Page : Type*} [DecidableEq Page]
noncomputable section

theorem paymentWindow_upward {input : Instance Page} {i : PaymentIndex input}
    {arrival service : Time} (ha : arrival ∈ paymentWindow input i)
    (has : arrival ≤ service) (hsp : service ≤ paymentTime input i) :
    service ∈ paymentWindow input i := by
  cases hp : previousIndex? input i with
  | none =>
      have ha' : arrival ∈ Icc (0 : Time) (paymentTime input i) := by
        simpa [paymentWindow, hp] using ha
      simpa [paymentWindow, hp] using
        (show service ∈ Icc (0 : Time) (paymentTime input i) from ⟨bot_le, hsp⟩)
  | some previous =>
      cases he : evictionTime? input i with
      | none => simp [paymentWindow, hp, he] at ha
      | some eviction =>
          have ha' : arrival ∈ Ioc eviction (paymentTime input i) := by
            simpa [paymentWindow, hp, he] using ha
          simpa [paymentWindow, hp, he] using
            (show service ∈ Ioc eviction (paymentTime input i) from
              ⟨ha'.1.trans_le has, hsp⟩)

/-- If the comparator does not already hold a request's page at its arrival,
serving it strictly before payment `i` forces a comparator fetch in `W_i`. -/
theorem isClassA_of_nonhit_serviceTime_lt
    (input : Instance Page) (comparator : Schedule Page)
    (i : PaymentIndex input) (request : Request Page)
    (hpagePayment : request.page = (payment input i).page)
    (harrival : request.arrival ∈ paymentWindow input i)
    (hnotHit : request.page ∉ comparator.cacheBefore request.arrival)
    {service : Time} (hservice : comparator.serviceTime request = some service)
    (hlt : service < paymentTime input i) :
    IsClassA input comparator i := by
  have hcandidates : (comparator.serviceCandidates request).Nonempty := by
    unfold Schedule.serviceTime at hservice
    split at hservice
    · assumption
    · contradiction
  have hmin : service = (comparator.serviceCandidates request).min' hcandidates := by
    unfold Schedule.serviceTime at hservice
    split at hservice
    · injection hservice with heq
      exact heq.symm
    · contradiction
  have hmember : service ∈ comparator.serviceCandidates request := by
    rw [hmin]
    exact Finset.min'_mem _ _
  simp only [Schedule.serviceCandidates, hnotHit, ↓reduceIte] at hmember
  rw [List.mem_toFinset] at hmember
  obtain ⟨event, heventFiltered, htime⟩ := List.mem_map.mp hmember
  obtain ⟨hevent, hcondition⟩ := List.mem_filter.mp heventFiltered
  simp only [decide_eq_true_eq] at hcondition
  rcases hcondition with ⟨harrivalEvent, hpage⟩
  refine ⟨event, hevent, ?_, ?_⟩
  · exact hpage.symm.trans hpagePayment
  · rw [htime]
    exact paymentWindow_upward harrival (by simpa [htime] using harrivalEvent)
      (le_of_lt hlt)

/-- Consequently, outside class A a non-hit cannot be served before the FIFO
payment.  Feasibility supplies existence of its service time. -/
theorem serviceTime_ge_paymentTime_of_not_classA_nonhit
    (input : Instance Page) (comparator : Schedule Page)
    (feasible : comparator.Feasible input) (i : PaymentIndex input)
    (request : Request Page)
    (hrequest : request ∈ input.requests)
    (hpagePayment : request.page = (payment input i).page)
    (harrival : request.arrival ∈ paymentWindow input i)
    (hnotA : ¬ IsClassA input comparator i)
    (hnotHit : request.page ∉ comparator.cacheBefore request.arrival) :
    ∃ service, comparator.serviceTime request = some service ∧
      paymentTime input i ≤ service := by
  have hcandidates := feasible.eventuallyServed request hrequest
  have hservice : comparator.serviceTime request =
      some ((comparator.serviceCandidates request).min' hcandidates) := by
    simp [Schedule.serviceTime, hcandidates]
  refine ⟨_, hservice, ?_⟩
  by_contra hnot
  have hlt : (comparator.serviceCandidates request).min' hcandidates <
      paymentTime input i := lt_of_not_ge hnot
  exact hnotA (isClassA_of_nonhit_serviceTime_lt input comparator i request
    hpagePayment harrival hnotHit hservice hlt)

theorem isClassD_of_paymentClass_eq (input : Instance Page)
    (comparator : Schedule Page) (i : PaymentIndex input)
    (hclass : paymentClass input comparator i = .D) :
    IsClassD input comparator i := by
  by_contra hnotD
  by_cases hA : IsClassA input comparator i
  · simp [paymentClass, hA] at hclass
  · simp only [paymentClass, hA, if_false, hnotD] at hclass
    generalize previousTime? input i = previous at hclass
    generalize relevantResidencies input comparator i = intervals at hclass
    cases previous <;> cases intervals <;> simp_all
    split at hclass <;> contradiction

/-- The semantic core of the paper's class-D paragraph: every request in the
FIFO batch is served by the comparator no earlier than the FIFO payment. -/
theorem classD_serviceTime_ge_paymentTime
    (input : Instance Page) (comparator : Schedule Page)
    (feasible : comparator.Feasible input) (i : PaymentIndex input)
    (request : Request Page) (hrequest : request ∈ input.requests)
    (hpagePayment : request.page = (payment input i).page)
    (harrival : request.arrival ∈ paymentWindow input i)
    (hclassD : IsClassD input comparator i) :
    ∃ service, comparator.serviceTime request = some service ∧
      paymentTime input i ≤ service := by
  have hnotHit : request.page ∉ comparator.cacheBefore request.arrival := by
    intro hhit
    obtain ⟨interval, hinterval, hipage, hicontains⟩ :=
      residency_of_mem_cacheBefore comparator feasible hhit
    have hrelevant : interval ∈ relevantResidencies input comparator i := by
      simp only [relevantResidencies, List.mem_filter, decide_eq_true_eq]
      refine ⟨hinterval, hipage.trans hpagePayment, request.arrival, harrival, hicontains⟩
    rw [hclassD.2] at hrelevant
    simp at hrelevant
  exact serviceTime_ge_paymentTime_of_not_classA_nonhit input comparator feasible
    i request hrequest hpagePayment harrival hclassD.1 hnotHit

end
end PagingWithDelay.Competitive
