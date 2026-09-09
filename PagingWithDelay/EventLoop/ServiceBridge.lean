import PagingWithDelay.EventLoop.PaymentAccounting

namespace PagingWithDelay

variable {Page : Type*} [DecidableEq Page]

noncomputable section

namespace Schedule

/-- A convenient elimination rule for the definition of `serviceTime`: a
candidate which is no later than every other candidate is the derived service
time.  In the FIFO proof the distinguished candidate is the payment which
removes the occurrence from `pending`. -/
theorem serviceTime_eq_some_of_le_candidates
    (schedule : Schedule Page) (request : Request Page) (time : Time)
    (hmem : time ∈ schedule.serviceCandidates request)
    (hle : ∀ candidate ∈ schedule.serviceCandidates request, time ≤ candidate) :
    schedule.serviceTime request = some time := by
  have hne : (schedule.serviceCandidates request).Nonempty := ⟨time, hmem⟩
  rw [serviceTime, dif_pos hne]
  congr 1
  apply le_antisymm
  · exact Finset.min'_le _ _ hmem
  · exact hle _ (Finset.min'_mem _ _)

theorem serviceDelay_eq_of_serviceTime
    (schedule : Schedule Page) (request : Request Page) (time : Time)
    (hservice : schedule.serviceTime request = some time) :
    schedule.serviceDelay request = time - request.arrival := by
  unfold serviceDelay
  rw [hservice]
  rfl

theorem requestCost_eq_of_serviceTime
    (schedule : Schedule Page) (request : Request Page) (time : Time)
    (hservice : schedule.serviceTime request = some time) :
    schedule.requestCost request = request.delay (time - request.arrival) := by
  simp [requestCost, serviceDelay_eq_of_serviceTime _ _ _ hservice]

/-- A public cache hit is served at its arrival time.  This follows from the
derived candidate semantics: every fetch candidate is constrained to occur no
earlier than arrival. -/
theorem serviceTime_eq_arrival_of_mem_cacheBefore
    (schedule : Schedule Page) (request : Request Page)
    (hhit : request.page ∈ schedule.cacheBefore request.arrival) :
    schedule.serviceTime request = some request.arrival := by
  apply serviceTime_eq_some_of_le_candidates
  · simp [serviceCandidates, hhit]
  · intro candidate hcandidate
    simp only [serviceCandidates, hhit, if_pos, Finset.mem_insert] at hcandidate
    rcases hcandidate with rfl | hcandidate
    · exact le_rfl
    · rw [List.mem_toFinset] at hcandidate
      obtain ⟨event, hevent, rfl⟩ := List.mem_map.mp hcandidate
      exact (of_decide_eq_true (List.mem_filter.mp hevent).2).1

/-- Consequently a cache hit contributes zero delay cost. -/
theorem requestCost_eq_zero_of_mem_cacheBefore
    (schedule : Schedule Page) (request : Request Page)
    (hhit : request.page ∈ schedule.cacheBefore request.arrival) :
    schedule.requestCost request = 0 := by
  rw [requestCost_eq_of_serviceTime schedule request request.arrival
    (serviceTime_eq_arrival_of_mem_cacheBefore schedule request hhit)]
  simp [request.delay_zero]

end Schedule

namespace FIFO

/-- Erasing a payment to the public event preserves its time and fetched
page.  Keeping this map named makes later occurrence-to-event arguments much
less dependent on simplifier details. -/
def Payment.fetchEvent (payment : Payment Page) : FetchEvent Page where
  time := payment.time
  fetched := payment.page
  cacheAfter := payment.queueAfter.toFinset

/-! `simp`-normal forms for the erased event.  These are `rfl` lemmas, so they
leave no trace in the proof terms, but the cache-trace proofs below need them
as rewrite rules. -/

@[simp] theorem Payment.fetchEvent_time (payment : Payment Page) :
    payment.fetchEvent.time = payment.time := rfl

@[simp] theorem Payment.fetchEvent_fetched (payment : Payment Page) :
    payment.fetchEvent.fetched = payment.page := rfl

@[simp] theorem Payment.fetchEvent_cacheAfter (payment : Payment Page) :
    payment.fetchEvent.cacheAfter = payment.queueAfter.toFinset := rfl

/-- Membership in a recorded batch supplies a public service candidate.  The
remaining run invariants only have to establish that this candidate is the
earliest one. -/
theorem payment_time_mem_serviceCandidates
    (payments : List (Payment Page)) (payment : Payment Page)
    (occurrence : Occurrence Page)
    (hpayment : payment ∈ payments)
    (harrival : occurrence.request.arrival ≤ payment.time)
    (hpage : occurrence.request.page = payment.page) :
    payment.time ∈
      (Schedule.mk (payments.map Payment.fetchEvent)).serviceCandidates
        occurrence.request := by
  unfold Schedule.serviceCandidates
  have hfetch : payment.fetchEvent ∈ payments.map Payment.fetchEvent := by
    exact List.mem_map.mpr ⟨payment, hpayment, rfl⟩
  have hfiltered : payment.fetchEvent ∈
      (payments.map Payment.fetchEvent).filter fun event =>
        occurrence.request.arrival ≤ event.time ∧
          occurrence.request.page = event.fetched := by
    simp only [List.mem_filter]
    exact ⟨hfetch, by simp [harrival, hpage]⟩
  have htime : payment.time ∈
      (((payments.map Payment.fetchEvent).filter fun event =>
        occurrence.request.arrival ≤ event.time ∧
          occurrence.request.page = event.fetched).map FetchEvent.time).toFinset := by
    rw [List.mem_toFinset]
    exact List.mem_map.mpr ⟨payment.fetchEvent, hfiltered, rfl⟩
  split
  · exact Finset.mem_insert_of_mem htime
  · exact htime

end FIFO
end
end PagingWithDelay
