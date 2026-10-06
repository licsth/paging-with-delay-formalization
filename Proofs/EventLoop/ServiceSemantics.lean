import Proofs.EventLoop.PaymentOrder
import Proofs.EventLoop.ServiceBridge
import Proofs.EventLoop.OccurrencePartition
import Proofs.EventLoop.History

/-! Proof-local invariants connecting FIFO's internal queue with its public
cache trace.  Nothing in this file is part of the model. -/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page] {trigger : Trigger}
noncomputable section

def prefixSchedule (input : Instance Page) (state : State Page) : Schedule Page :=
  ⟨input.initialCache.toFinset, state.payments.map Payment.fetchEvent⟩

/-- How the internal queue and the recorded batches look in the public cache trace. -/
structure ServiceTraceInvariant (input : Instance Page) (state : State Page) : Prop where
  queue : state.queue.toFinset = state.payments.foldl
    (fun _ payment => payment.queueAfter.toFinset) input.initialCache.toFinset
  pending_miss : ∀ occurrence ∈ state.pending,
    occurrence.request.page ∉ (prefixSchedule input state).cacheBefore occurrence.request.arrival
  served_miss : ∀ payment ∈ state.payments, ∀ occurrence ∈ payment.served,
    occurrence.request.page ∉ (prefixSchedule input state).cacheBefore occurrence.request.arrival
  pending_after : ∀ occurrence ∈ state.pending, ∀ payment ∈ state.payments,
    occurrence.request.page = payment.page → payment.time < occurrence.request.arrival

/-- At an arrival still to come, the public cache is the internal queue. -/
theorem prefixSchedule_cacheBefore_eq_queue {input : Instance Page}
    {state : State Page} (hinv : ServiceTraceInvariant input state)
    (hstrict : History.StrictUnseen state)
    {occurrence : Occurrence Page} (hunseen : occurrence ∈ state.unseen) :
    (prefixSchedule input state).cacheBefore occurrence.request.arrival =
      state.queue.toFinset := by
  have hlt : ∀ payment ∈ state.payments, payment.time < occurrence.request.arrival :=
    fun payment hp => hstrict payment hp occurrence hunseen
  rw [hinv.queue]
  unfold prefixSchedule Schedule.cacheBefore
  generalize input.initialCache.toFinset = initial
  revert hlt
  induction state.payments generalizing initial with
  | nil => exact fun _ => rfl
  | cons payment rest ih => intro hlt; simp_all

/-- A payment does not change the public cache before its time. -/
private theorem cacheBefore_step_payment (input : Instance Page) (state : State Page)
    (time : Time) (page : Page) {arrival : Time} (hfuture : arrival ≤ time) :
    (prefixSchedule input (step input state (.payment time page))).cacheBefore arrival =
      (prefixSchedule input state).cacheBefore arrival := by
  simp [prefixSchedule, step, Schedule.cacheBefore, not_lt_of_ge hfuture]

theorem Reachable.serviceTraceInvariant {input : Instance Page} {state : State Page}
    (h : Reachable trigger input state) : ServiceTraceInvariant input state := by
  induction h with
  | initial => exact ⟨by simp [initialState], by simp [initialState], by simp [initialState],
      by simp [initialState]⟩
  | @step state action hr haction ih =>
      have hstrict := hr.strictUnseen
      have hpendingArrival := hr.history.1
      cases action with
      | arrival occurrence =>
          have hunseen := arrival_mem_unseen haction
          -- the arriving request becomes pending only on a miss, and arrives after every payment
          have hnew : ∀ candidate ∈ (FIFO.step input state (.arrival occurrence)).pending,
              candidate ∈ state.pending ∨
                (candidate = occurrence ∧ occurrence.request.page ∉ state.queue) := by
            intro candidate hc
            simp only [FIFO.step] at hc
            split at hc
            · exact .inl hc
            · rename_i hmiss
              rcases List.mem_append.mp hc with hc | hc
              · exact .inl hc
              · exact .inr ⟨List.mem_singleton.1 hc, hmiss⟩
          refine ⟨ih.queue, fun candidate hc => ?_, ih.served_miss, fun candidate hc => ?_⟩
          · rcases hnew candidate hc with hold | ⟨rfl, hmiss⟩
            · exact ih.pending_miss candidate hold
            · change candidate.request.page ∉ (prefixSchedule input state).cacheBefore _
              rw [prefixSchedule_cacheBefore_eq_queue ih hstrict hunseen]
              simpa using hmiss
          · rcases hnew candidate hc with hold | ⟨rfl, -⟩
            · exact ih.pending_after candidate hold
            · exact fun payment hm _ => hstrict payment hm candidate hunseen
      | payment time page =>
          have hnow := nextPayment_now_le (nextAction_payment_selected haction)
          have hfuture (o : Occurrence Page) (ho : o ∈ state.pending) :
              o.request.arrival ≤ time := (hpendingArrival o ho).trans hnow
          refine ⟨by simp [FIFO.step], fun o ho => ?_, fun candidate hm o ho => ?_,
            fun o ho candidate hm heq => ?_⟩
          · have hold := (List.mem_filter.mp ho).1
            rw [cacheBefore_step_payment _ _ _ _ (hfuture o hold)]
            exact ih.pending_miss o hold
          · simp only [FIFO.step, List.mem_append, List.mem_singleton] at hm
            rcases hm with hold | rfl
            · rw [cacheBefore_step_payment _ _ _ _ (((hr.history.2 candidate hold o ho).2).trans
                ((hr.timeInvariant.payments_before_now candidate hold).trans hnow))]
              exact ih.served_miss candidate hold o ho
            · have hold := (List.mem_filter.mp ho).1
              rw [cacheBefore_step_payment _ _ _ _ (hfuture o hold)]
              exact ih.pending_miss o hold
          · have ho' := List.mem_filter.mp ho
            simp only [FIFO.step, List.mem_append, List.mem_singleton] at hm
            rcases hm with hold | rfl
            · exact ih.pending_after o ho'.1 candidate hold heq
            · exact absurd heq (of_decide_eq_true ho'.2)

/-- For every served occurrence, any same-page payment is either too early
to serve it or no earlier than its recorded payment. -/
def ServiceMinimalInvariant (state : State Page) : Prop :=
  ∀ payment ∈ state.payments, ∀ occurrence ∈ payment.served,
    ∀ candidate ∈ state.payments, occurrence.request.page = candidate.page →
      candidate.time < occurrence.request.arrival ∨ payment.time ≤ candidate.time

theorem Reachable.serviceMinimalInvariant {input : Instance Page} {state : State Page}
    (h : Reachable trigger input state) : ServiceMinimalInvariant state := by
  induction h with
  | initial => simp [ServiceMinimalInvariant, initialState]
  | @step state action hr haction ih =>
      cases action with
      | arrival occurrence => simpa [FIFO.step, ServiceMinimalInvariant] using ih
      | payment time page =>
          have hnow := nextPayment_now_le (nextAction_payment_selected haction)
          intro payment hpayment occurrence hserved candidate hcandidate hpage
          simp only [FIFO.step, List.mem_append, List.mem_singleton] at hpayment hcandidate
          rcases hpayment with holdPayment | rfl
          · rcases hcandidate with holdCandidate | rfl
            · exact ih payment holdPayment occurrence hserved candidate holdCandidate hpage
            · exact .inr ((hr.timeInvariant.payments_before_now payment holdPayment).trans hnow)
          · rcases hcandidate with holdCandidate | rfl
            · exact .inl (hr.serviceTraceInvariant.pending_after occurrence
                (List.mem_filter.mp hserved).1 candidate holdCandidate hpage)
            · exact .inr le_rfl

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
      (run trigger input (2 * input.requests.length) (initialState input)).payments)
    (occurrence : Occurrence Page) (hserved : occurrence ∈ payment.served) :
    (schedule trigger input).requestCost occurrence.request =
      occurrence.request.delay (payment.time - occurrence.request.arrival) := by
  let final := run trigger input (2 * input.requests.length) (initialState input)
  have hr := reachable_final (trigger := trigger) input
  have hbatch := hr.history.2 payment hpayment occurrence hserved
  change (Schedule.mk input.initialCache.toFinset
      (final.payments.map Payment.fetchEvent)).requestCost occurrence.request = _
  refine payment_requestCost_eq_of_minimal _ final.payments payment occurrence hpayment
    hbatch.2 hbatch.1 (hr.serviceTraceInvariant.served_miss payment hpayment occurrence hserved)
    fun candidate hcandidate harrival hpage => ?_
  exact (hr.serviceMinimalInvariant payment hpayment occurrence hserved candidate hcandidate
    hpage).resolve_left (not_lt_of_ge harrival)

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

theorem Reachable.droppedHitInvariant {input : Instance Page} {state : State Page}
    (h : Reachable trigger input state) : DroppedHitInvariant input state := by
  induction h with
  | initial => exact fun occurrence hinput hunseen => absurd hinput hunseen
  | @step state action hr haction ih =>
      intro original hinput hunseen hpending hserved
      cases action with
      | arrival occurrence =>
          have hu := (nextAction_arrival haction).1
          have hnow := hr.timeInvariant.now_before_unseen occurrence (arrival_mem_unseen haction)
          change _ ≤ occurrence.request.arrival ∧
            original.request.page ∈ (prefixSchedule input state).cacheBefore _
          by_cases heq : original = occurrence
          · subst original
            refine ⟨le_rfl, ?_⟩
            by_cases hhit : occurrence.request.page ∈ state.queue
            · rw [prefixSchedule_cacheBefore_eq_queue hr.serviceTraceInvariant hr.strictUnseen
                (arrival_mem_unseen haction)]
              simpa using hhit
            · exact absurd (by simp [FIFO.step, hhit]) hpending
          · have hold := ih original hinput
              (by rw [hu]; simpa [heq, FIFO.step] using hunseen)
              (fun hold => hpending (by simp only [FIFO.step]; split <;> simp [hold]))
              (by simpa [FIFO.step] using hserved)
            exact ⟨hold.1.trans hnow, hold.2⟩
      | payment time page =>
          have hnow := nextPayment_now_le (nextAction_payment_selected haction)
          have hold := ih original hinput (by simpa [FIFO.step] using hunseen)
            (fun hold => by
              by_cases hpage : original.request.page = page
              · exact hserved (by simp [FIFO.step, hold, hpage])
              · exact hpending (by simp [FIFO.step, hold, hpage]))
            (fun hold => hserved (by simp [FIFO.step, hold]))
          exact ⟨hold.1.trans hnow, by
            rw [cacheBefore_step_payment _ _ _ _ (hold.1.trans hnow)]; exact hold.2⟩

theorem final_dropped_occurrence_is_hit (input : Instance Page)
    (occurrence : Occurrence Page) (hinput : occurrence ∈ enumerate input.requests)
    (hnotServed : occurrence ∉
      (run trigger input (2 * input.requests.length) (initialState input)).payments.flatMap
        Payment.served) :
    occurrence.request.page ∈
      (schedule trigger input).cacheBefore occurrence.request.arrival := by
  obtain ⟨hunseen, hpending⟩ := final_unseen_eq_nil_and_pending_eq_nil (trigger := trigger) input
  exact ((reachable_final input).droppedHitInvariant occurrence hinput (by simp [hunseen])
    (by simp [hpending]) hnotServed).2

end
end PagingWithDelay.FIFO
