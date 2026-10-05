import Proofs.EventLoop.PaymentOrder
import Proofs.EventLoop.ServiceBridge
import Proofs.EventLoop.OccurrencePartition
import Proofs.EventLoop.History

/-! Proof-local invariants connecting FIFO's internal queue with its public
cache trace.  Nothing in this file is part of the model. -/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page] {δ : Cost}
noncomputable section

def prefixSchedule (input : Instance Page) (state : State Page) : Schedule Page :=
  ⟨input.initialCache.toFinset, state.payments.map Payment.fetchEvent⟩

def ServiceTraceInvariant (input : Instance Page) (state : State Page) : Prop :=
  state.queue.toFinset = state.payments.foldl
      (fun _ payment => payment.queueAfter.toFinset) input.initialCache.toFinset ∧
    (∀ payment ∈ state.payments, ∀ occurrence ∈ state.unseen,
      payment.time < occurrence.request.arrival) ∧
    (∀ occurrence ∈ state.pending,
      occurrence.request.page ∉
        (prefixSchedule input state).cacheBefore occurrence.request.arrival) ∧
    (∀ payment ∈ state.payments, ∀ occurrence ∈ payment.served,
      occurrence.request.page ∉
        (prefixSchedule input state).cacheBefore occurrence.request.arrival) ∧
    (∀ payment ∈ state.payments, ∀ occurrence ∈ payment.served,
      occurrence.request.arrival ≤ payment.time) ∧
    (∀ occurrence ∈ state.pending, occurrence.request.arrival ≤ state.now) ∧
    (∀ occurrence ∈ state.pending, ∀ payment ∈ state.payments,
      occurrence.request.page = payment.page →
        payment.time < occurrence.request.arrival)

private theorem fold_events_eq_fold_payments (payments : List (Payment Page)) :
    (payments.map Payment.fetchEvent).foldl
        (fun current event => if event.time < t then event.cacheAfter else current) initial =
      payments.foldl
        (fun current payment => if payment.time < t then payment.queueAfter.toFinset else current)
        initial := by
  induction payments generalizing initial with
  | nil => rfl
  | cons payment rest ih => simp [ih]

private theorem fold_if_all_lt (payments : List (Payment Page))
    (h : ∀ payment ∈ payments, payment.time < t) :
    payments.foldl
        (fun current payment => if payment.time < t then payment.queueAfter.toFinset else current)
        initial =
      payments.foldl (fun _ payment => payment.queueAfter.toFinset) initial := by
  induction payments generalizing initial with
  | nil => rfl
  | cons payment rest ih =>
      simp only [List.foldl_cons]
      rw [if_pos (h payment (by simp))]
      exact ih (fun p hp => h p (by simp [hp]))

theorem prefixSchedule_cacheBefore_eq_queue {input : Instance Page}
    {state : State Page} (hinv : ServiceTraceInvariant input state)
    {occurrence : Occurrence Page} (hunseen : occurrence ∈ state.unseen) :
    (prefixSchedule input state).cacheBefore occurrence.request.arrival =
      state.queue.toFinset := by
  rw [hinv.1]
  unfold prefixSchedule Schedule.cacheBefore
  rw [fold_events_eq_fold_payments]
  exact fold_if_all_lt _ (fun payment hp => hinv.2.1 payment hp occurrence hunseen)

theorem initial_serviceTraceInvariant (input : Instance Page) :
    ServiceTraceInvariant input (initialState input) := by
  simp [ServiceTraceInvariant, initialState]

private theorem arrival_unseen_eq {state : State Page} {occurrence : Occurrence Page}
    (ha : nextAction? δ state = some (.arrival occurrence)) :
    state.unseen = occurrence :: state.unseen.tail := by
  unfold nextAction? at ha
  cases hu : state.unseen with
  | nil => cases hp : nextPayment? δ state <;> simp [hu, hp] at ha
  | cons head tail =>
      cases hp : nextPayment? δ state with
      | none => simp only [hu, hp] at ha; injection ha with heq; cases heq; simp
      | some pair =>
          simp only [hu, hp] at ha
          split at ha
          · injection ha with heq; cases heq; simp
          · simp at ha

private theorem selected_payment_lt_unseen {state : State Page} {time : Time}
    {page : Page} (htime : TimeInvariant state)
    (ha : nextAction? δ state = some (.payment time page))
    {occurrence : Occurrence Page} (ho : occurrence ∈ state.unseen) :
    time < occurrence.request.arrival := by
  unfold nextAction? at ha
  cases hu : state.unseen with
  | nil => simp [hu] at ho
  | cons head tail =>
      cases hp : nextPayment? δ state with
      | none => simp [hu, hp] at ha
      | some pair =>
          rcases pair with ⟨t, p⟩
          simp only [hu, hp] at ha
          split at ha
          · simp at ha
          · injection ha with heq
            cases heq
            have hhead : time < head.request.arrival := lt_of_not_ge (by assumption)
            rw [hu] at ho
            rcases List.mem_cons.mp ho with rfl | htail
            · exact hhead
            · have hc := htime.unseen_chronological
              rw [hu, List.pairwise_cons] at hc
              exact hhead.trans_le (hc.1 occurrence htail)

private theorem cacheBefore_append_future (initial : Finset Page)
    (payments : List (Payment Page)) (payment : Payment Page) {arrival : Time}
    (hfuture : arrival ≤ payment.time) :
    (Schedule.mk initial ((payments ++ [payment]).map Payment.fetchEvent)).cacheBefore
        arrival =
      (Schedule.mk initial (payments.map Payment.fetchEvent)).cacheBefore arrival := by
  unfold Schedule.cacheBefore
  simp [not_lt_of_ge hfuture]

/-- The cache trace invariant is preserved by one selected event.  All its
premises are independently proved event-loop invariants. -/
theorem step_serviceTraceInvariant (input : Instance Page) (state : State Page)
    (action : Action Page) (htime : TimeInvariant state)
    (hinv : ServiceTraceInvariant input state)
    (haction : nextAction? δ state = some action) :
    ServiceTraceInvariant input (step input state action) := by
  rcases hinv with ⟨hqueue, hunseen, hpendingMiss, hservedMiss,
    hservedArrival, hpendingArrival, hpendingPayments⟩
  cases action with
  | arrival occurrence =>
      have hu := arrival_unseen_eq haction
      have hoccurUnseen : occurrence ∈ state.unseen := by rw [hu]; simp
      have hcache := prefixSchedule_cacheBefore_eq_queue
        (show ServiceTraceInvariant input state from ⟨hqueue, hunseen, hpendingMiss,
          hservedMiss, hservedArrival, hpendingArrival, hpendingPayments⟩)
        hoccurUnseen
      simp only [step]
      constructor
      · exact hqueue
      constructor
      · intro payment hm candidate hc
        exact hunseen payment hm candidate (List.mem_of_mem_tail hc)
      constructor
      · intro candidate hc
        split at hc
        · exact hpendingMiss candidate hc
        · rcases List.mem_append.mp hc with hold | hnew
          · exact hpendingMiss candidate hold
          · have : candidate = occurrence := by simpa using hnew
            subst candidate
            change occurrence.request.page ∉
              (prefixSchedule input state).cacheBefore occurrence.request.arrival
            rw [hcache]
            simpa using (show occurrence.request.page ∉ state.queue from by assumption)
      constructor
      · exact hservedMiss
      constructor
      · exact hservedArrival
      constructor
      · intro candidate hc
        split at hc
        · exact (hpendingArrival candidate hc).trans
            (htime.now_before_unseen occurrence hoccurUnseen)
        · rcases List.mem_append.mp hc with hold | hnew
          · exact (hpendingArrival candidate hold).trans
              (htime.now_before_unseen occurrence hoccurUnseen)
          · have : candidate = occurrence := by simpa using hnew
            subst candidate
            exact le_rfl
      · intro candidate hc payment hm heq
        split at hc
        · exact hpendingPayments candidate hc payment hm heq
        · rcases List.mem_append.mp hc with hold | hnew
          · exact hpendingPayments candidate hold payment hm heq
          · have : candidate = occurrence := by simpa using hnew
            subst candidate
            exact hunseen payment hm occurrence hoccurUnseen
  | payment time page =>
      have hnow : state.now ≤ time := by
        have hs := nextAction_payment_selected haction
        rw [← nextPayment_time_eq hs]
        exact thresholdTime_ge_now state page
          (pending_of_mem_pendingPages (nextPayment_mem_pendingPages hs))
      let made : Payment Page :=
        { time := time, page := page,
          served := state.pending.filter fun o => o.request.page = page,
          queueAfter := insertPage input.cacheSize state.queue page }
      have hfuture (o : Occurrence Page) (ho : o ∈ state.pending) :
          o.request.arrival ≤ time := (hpendingArrival o ho).trans hnow
      simp only [step]
      constructor
      · simp
      constructor
      · intro candidate hm o ho
        rcases List.mem_append.mp hm with hold | hnew
        · exact hunseen candidate hold o ho
        · have : candidate = made := by simpa [made] using hnew
          subst candidate
          exact selected_payment_lt_unseen htime haction ho
      constructor
      · intro o ho
        have hold := (List.mem_filter.mp ho).1
        unfold prefixSchedule
        rw [cacheBefore_append_future _ state.payments made (hfuture o hold)]
        exact hpendingMiss o hold
      constructor
      · intro candidate hm o ho
        rcases List.mem_append.mp hm with hold | hnew
        · unfold prefixSchedule
          rw [cacheBefore_append_future _ state.payments made
              ((hservedArrival candidate hold o ho).trans
                ((htime.payments_before_now candidate hold).trans hnow))]
          exact hservedMiss candidate hold o ho
        · have : candidate = made := by simpa [made] using hnew
          subst candidate
          have hold := (List.mem_filter.mp ho).1
          unfold prefixSchedule
          rw [cacheBefore_append_future _ state.payments made (hfuture o hold)]
          exact hpendingMiss o hold
      constructor
      · intro candidate hm o ho
        rcases List.mem_append.mp hm with hold | hnew
        · exact hservedArrival candidate hold o ho
        · have : candidate = made := by simpa [made] using hnew
          subst candidate
          exact hfuture o (List.mem_filter.mp ho).1
      constructor
      · intro o ho
        exact hfuture o (List.mem_filter.mp ho).1
      · intro o ho candidate hm heq
        have hold := (List.mem_filter.mp ho).1
        rcases List.mem_append.mp hm with old | hnew
        · exact hpendingPayments o hold candidate old heq
        · have : candidate = made := by simpa [made] using hnew
          subst candidate
          exact False.elim ((of_decide_eq_true (List.mem_filter.mp ho).2) heq)

/-- For every served occurrence, any same-page payment is either too early
to serve it or no earlier than its recorded payment. -/
def ServiceMinimalInvariant (state : State Page) : Prop :=
  ∀ payment ∈ state.payments, ∀ occurrence ∈ payment.served,
    ∀ candidate ∈ state.payments, occurrence.request.page = candidate.page →
      candidate.time < occurrence.request.arrival ∨ payment.time ≤ candidate.time

theorem initial_serviceMinimalInvariant (input : Instance Page) :
    ServiceMinimalInvariant (initialState input) := by
  simp [ServiceMinimalInvariant, initialState]

theorem step_serviceMinimalInvariant (input : Instance Page) (state : State Page)
    (action : Action Page) (htime : TimeInvariant state)
    (htrace : ServiceTraceInvariant input state) (hminimal : ServiceMinimalInvariant state)
    (haction : nextAction? δ state = some action) :
    ServiceMinimalInvariant (step input state action) := by
  rcases htrace with ⟨_, _, _, _, _, _, hpendingPayments⟩
  cases action with
  | arrival occurrence => simpa [step, ServiceMinimalInvariant] using hminimal
  | payment time page =>
      have hnow : state.now ≤ time := by
        have hs := nextAction_payment_selected haction
        rw [← nextPayment_time_eq hs]
        exact thresholdTime_ge_now state page
          (pending_of_mem_pendingPages (nextPayment_mem_pendingPages hs))
      intro payment hpayment occurrence hserved candidate hcandidate hpage
      simp only [step, List.mem_append, List.mem_singleton] at hpayment hcandidate
      rcases hpayment with holdPayment | rfl
      · rcases hcandidate with holdCandidate | rfl
        · exact hminimal payment holdPayment occurrence hserved candidate holdCandidate hpage
        · exact Or.inr ((htime.payments_before_now payment holdPayment).trans hnow)
      · have hservedOld := (List.mem_filter.mp hserved).1
        rcases hcandidate with holdCandidate | rfl
        · exact Or.inl (hpendingPayments occurrence hservedOld candidate holdCandidate hpage)
        · exact Or.inr le_rfl

theorem run_serviceInvariants (input : Instance Page) : ∀ fuel state,
    TimeInvariant state → BelowThreshold δ state → ServiceTraceInvariant input state →
      ServiceMinimalInvariant state →
      ServiceTraceInvariant input (run δ input fuel state) ∧
        ServiceMinimalInvariant (run δ input fuel state) := by
  intro fuel
  induction fuel with
  | zero => intro state _ _ ht hm; exact ⟨ht, hm⟩
  | succ fuel ih =>
      intro state htime hbelow htrace hminimal
      rw [run]
      cases ha : nextAction? δ state with
      | none => exact ⟨htrace, hminimal⟩
      | some action =>
          exact ih _ (step_timeInvariant input state action htime ha)
            (step_belowThreshold input state action hbelow ha)
            (step_serviceTraceInvariant input state action htime htrace ha)
            (step_serviceMinimalInvariant input state action htime htrace hminimal ha)

theorem final_serviceInvariants (input : Instance Page) :
    let final := run δ input (2 * input.requests.length) (initialState input)
    ServiceTraceInvariant input final ∧ ServiceMinimalInvariant final := by
  exact run_serviceInvariants input _ _ (initial_timeInvariant input)
    (initial_belowThreshold input) (initial_serviceTraceInvariant input)
    (initial_serviceMinimalInvariant input)

/-- A payment is the public service time of one of its requests as soon as
the runtime proof supplies the two genuinely semantic facts: the request was
not already resident on arrival, and no eligible fetch of the same page is
earlier.  Keeping this bridge separate prevents either fact from being
smuggled into the definition of FIFO accounting. -/
theorem payment_serviceTime_eq_of_minimal (initial : Finset Page)
    (payments : List (Payment Page)) (payment : Payment Page)
    (occurrence : Occurrence Page)
    (hpayment : payment ∈ payments)
    (harrival : occurrence.request.arrival ≤ payment.time)
    (hpage : occurrence.request.page = payment.page)
    (hmiss : occurrence.request.page ∉
      (Schedule.mk initial (payments.map Payment.fetchEvent)).cacheBefore
        occurrence.request.arrival)
    (hminimal : ∀ candidate ∈ payments,
      occurrence.request.arrival ≤ candidate.time →
      occurrence.request.page = candidate.page →
      payment.time ≤ candidate.time) :
    (Schedule.mk initial (payments.map Payment.fetchEvent)).serviceTime occurrence.request =
      some payment.time := by
  let schedule : Schedule Page := ⟨initial, payments.map Payment.fetchEvent⟩
  change schedule.serviceTime occurrence.request = some payment.time
  apply Schedule.serviceTime_eq_some_of_le_candidates
  · exact payment_time_mem_serviceCandidates initial payments payment occurrence hpayment
      harrival hpage
  · intro time htime
    unfold Schedule.serviceCandidates at htime
    rw [if_neg hmiss] at htime
    rw [List.mem_toFinset] at htime
    obtain ⟨event, hevent, rfl⟩ := List.mem_map.mp htime
    obtain ⟨heventMem, heventValid⟩ := List.mem_filter.mp hevent
    obtain ⟨candidate, hcandidate, rfl⟩ := List.mem_map.mp heventMem
    exact hminimal candidate hcandidate
      (of_decide_eq_true heventValid).1
      (of_decide_eq_true heventValid).2

/-- Cost form of `payment_serviceTime_eq_of_minimal`. -/
theorem payment_requestCost_eq_of_minimal (initial : Finset Page)
    (payments : List (Payment Page)) (payment : Payment Page)
    (occurrence : Occurrence Page)
    (hpayment : payment ∈ payments)
    (harrival : occurrence.request.arrival ≤ payment.time)
    (hpage : occurrence.request.page = payment.page)
    (hmiss : occurrence.request.page ∉
      (Schedule.mk initial (payments.map Payment.fetchEvent)).cacheBefore
        occurrence.request.arrival)
    (hminimal : ∀ candidate ∈ payments,
      occurrence.request.arrival ≤ candidate.time →
      occurrence.request.page = candidate.page →
      payment.time ≤ candidate.time) :
    (Schedule.mk initial (payments.map Payment.fetchEvent)).requestCost occurrence.request =
      occurrence.request.delay (payment.time - occurrence.request.arrival) := by
  apply Schedule.requestCost_eq_of_serviceTime
  exact payment_serviceTime_eq_of_minimal initial payments payment occurrence hpayment
    harrival hpage hmiss hminimal

/-- Every occurrence recorded in a final payment batch has exactly the
public delay cost displayed in that batch. -/
theorem final_served_requestCost_eq (input : Instance Page)
    (payment : Payment Page)
    (hpayment : payment ∈
      (run δ input (2 * input.requests.length) (initialState input)).payments)
    (occurrence : Occurrence Page) (hserved : occurrence ∈ payment.served) :
    (schedule δ input).requestCost occurrence.request =
      occurrence.request.delay (payment.time - occurrence.request.arrival) := by
  let final := run δ input (2 * input.requests.length) (initialState input)
  have hinvariants := final_serviceInvariants (δ := δ) input
  have htrace : ServiceTraceInvariant input final := hinvariants.1
  have hminimal : ServiceMinimalInvariant final := hinvariants.2
  have hmiss := htrace.2.2.2.1 payment hpayment occurrence hserved
  have harrival := htrace.2.2.2.2.1 payment hpayment occurrence hserved
  have hpage :=
    (History.final_validBatches input payment hpayment
      occurrence hserved).1
  change (Schedule.mk input.initialCache.toFinset
      (final.payments.map Payment.fetchEvent)).requestCost occurrence.request = _
  apply payment_requestCost_eq_of_minimal _ final.payments payment occurrence
    hpayment harrival hpage hmiss
  intro candidate hcandidate hcandidateArrival hcandidatePage
  rcases hminimal payment hpayment occurrence hserved candidate hcandidate
      hcandidatePage with htooEarly | hlater
  · exact False.elim ((not_lt_of_ge hcandidateArrival) htooEarly)
  · exact hlater

/-- Any authentic occurrence which has left all runtime work lists without
being put in a payment batch was a cache hit.  The arrival bound is retained
because it is precisely what proves that later payments do not alter the
public cache observed at that arrival. -/
def DroppedHitInvariant (input : Instance Page) (state : State Page) : Prop :=
  ∀ occurrence ∈ enumerate input.requests,
    occurrence ∉ state.unseen → occurrence ∉ state.pending →
    occurrence ∉ state.payments.flatMap Payment.served →
      occurrence.request.arrival ≤ state.now ∧
        occurrence.request.page ∈
          (prefixSchedule input state).cacheBefore occurrence.request.arrival

theorem initial_droppedHitInvariant (input : Instance Page) :
    DroppedHitInvariant input (initialState input) := by
  intro occurrence hinput hunseen
  exact False.elim (hunseen hinput)

theorem step_droppedHitInvariant (input : Instance Page) (state : State Page)
    (action : Action Page) (htime : TimeInvariant state)
    (htrace : ServiceTraceInvariant input state)
    (hhits : DroppedHitInvariant input state)
    (haction : nextAction? δ state = some action) :
    DroppedHitInvariant input (step input state action) := by
  intro original hinput hunseen hpending hserved
  cases action with
  | arrival occurrence =>
      have hu := arrival_unseen_eq haction
      by_cases heq : original = occurrence
      · subst original
        constructor
        · exact le_rfl
        · by_cases hhit : occurrence.request.page ∈ state.queue
          · have hcache := prefixSchedule_cacheBefore_eq_queue htrace
              (show occurrence ∈ state.unseen by rw [hu]; simp)
            change occurrence.request.page ∈
              (prefixSchedule input state).cacheBefore occurrence.request.arrival
            rw [hcache]
            simpa using hhit
          · exfalso
            apply hpending
            simp [step, hhit]
      · have hunseenOld : original ∉ state.unseen := by
          rw [hu]
          simp only [List.mem_cons, not_or]
          exact ⟨heq, by simpa only [step] using hunseen⟩
        have hpendingOld : original ∉ state.pending := by
          intro hold
          apply hpending
          simp only [step]
          split
          · exact hold
          · exact List.mem_append_left _ hold
        have hservedOld : original ∉ state.payments.flatMap Payment.served := by
          simpa [step] using hserved
        have hold := hhits original hinput hunseenOld hpendingOld hservedOld
        constructor
        · exact hold.1.trans (htime.now_before_unseen occurrence (by rw [hu]; simp))
        · change original.request.page ∈
            (prefixSchedule input state).cacheBefore original.request.arrival
          exact hold.2
  | payment time page =>
      have hnow : state.now ≤ time := by
        have hs := nextAction_payment_selected haction
        rw [← nextPayment_time_eq hs]
        exact thresholdTime_ge_now state page
          (pending_of_mem_pendingPages (nextPayment_mem_pendingPages hs))
      have hunseenOld : original ∉ state.unseen := by simpa [step] using hunseen
      have hpendingOld : original ∉ state.pending := by
        intro hold
        by_cases hpage : original.request.page = page
        · apply hserved
          simp [step, hold, hpage]
        · apply hpending
          simp [step, hold, hpage]
      have hservedOld : original ∉ state.payments.flatMap Payment.served := by
        intro hold
        apply hserved
        simp [step, hold]
      have hold := hhits original hinput hunseenOld hpendingOld hservedOld
      constructor
      · exact hold.1.trans hnow
      · unfold prefixSchedule
        simp only [step]
        rw [cacheBefore_append_future _ state.payments
          { time := time, page := page,
            served := state.pending.filter fun o => o.request.page = page,
            queueAfter := insertPage input.cacheSize state.queue page }
          (hold.1.trans hnow)]
        exact hold.2

theorem run_droppedHitInvariant (input : Instance Page) : ∀ fuel state,
    TimeInvariant state → BelowThreshold δ state → ServiceTraceInvariant input state →
      DroppedHitInvariant input state →
      DroppedHitInvariant input (run δ input fuel state) := by
  intro fuel
  induction fuel with
  | zero => exact fun _ _ _ _ h => h
  | succ fuel ih =>
      intro state htime hbelow htrace hhits
      rw [run]
      cases ha : nextAction? δ state with
      | none => exact hhits
      | some action =>
          exact ih _ (step_timeInvariant input state action htime ha)
            (step_belowThreshold input state action hbelow ha)
            (step_serviceTraceInvariant input state action htime htrace ha)
            (step_droppedHitInvariant input state action htime htrace hhits ha)

theorem final_dropped_occurrence_is_hit (input : Instance Page)
    (occurrence : Occurrence Page) (hinput : occurrence ∈ enumerate input.requests)
    (hnotServed : occurrence ∉
      (run δ input (2 * input.requests.length) (initialState input)).payments.flatMap
        Payment.served) :
    occurrence.request.page ∈
      (schedule δ input).cacheBefore occurrence.request.arrival := by
  let final := run δ input (2 * input.requests.length) (initialState input)
  have hfinished := final_unseen_eq_nil_and_pending_eq_nil (δ := δ) input
  have hinv := run_droppedHitInvariant (δ := δ) input (2 * input.requests.length)
    (initialState input)
    (initial_timeInvariant input) (initial_belowThreshold input)
    (initial_serviceTraceInvariant input) (initial_droppedHitInvariant input)
  change occurrence.request.page ∈
    (prefixSchedule input final).cacheBefore occurrence.request.arrival
  exact (hinv occurrence hinput (by simp [hfinished.1])
    (by simp [hfinished.2]) hnotServed).2

end
end PagingWithDelay.FIFO
