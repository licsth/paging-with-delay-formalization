import Proofs.EventLoop.ServiceSemantics

/-!
# Feasibility of the schedule produced by FIFO, for every trigger

An `Algorithm` in `Model.lean` must produce a feasible schedule on every
instance.  This file proves `(FIFO.schedule trigger input).Feasible input` for
every trigger, which `Algorithm.lean` uses to package the event loop as the
algorithm `FIFO.algorithm` that the public theorems name.  Nothing in the
argument constrains the trigger: a payment is legal whenever it is made.

Each of the five checks in `Schedule.Feasible` is discharged from an invariant
that the competitive proof already had to establish about `FIFO.run`:

| field | source |
| --- | --- |
| `initialCache` | the queue starts as `input.initialCache` (`schedule` records it) |
| `chronological` | `FIFO.final_payment_times_chronological` |
| `validTransitions` | `FreshPayments`: a payment page is absent from the replayed queue |
| `capacity` | `recentPages_length`, via `FreshPayments.queueAfter_at` |
| `eventuallyServed` | the hit/batch partition also used by `FIFO.algorithmCostClaim` |
-/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page] {trigger : Trigger}

noncomputable section

/-! ## Local facts about one FIFO replacement -/

omit [DecidableEq Page] in
private theorem mem_insertPage_self (capacity : ℕ) (queue : List Page) (page : Page) :
    page ∈ insertPage capacity queue page := by
  unfold insertPage
  split <;> simp

/-- A FIFO miss introduces precisely the requested page.  Replacement may drop
an old page, but it cannot introduce any other new one. -/
private theorem insertPage_toFinset_sdiff (capacity : ℕ) (queue : List Page)
    (page : Page) (hpage : page ∉ queue) :
    (insertPage capacity queue page).toFinset \ queue.toFinset = {page} := by
  ext candidate
  unfold insertPage
  split <;> simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_singleton, List.mem_append,
    List.mem_singleton] <;> grind [List.mem_of_mem_tail]

/-! ## Transition legality from an indexed cache history -/

/-- `Schedule.ValidTransitionsFrom` from a per-index description of the cache
after each event.  This is the only place where the local shape of
`ValidTransitionsFrom` is unfolded. -/
private theorem validTransitionsFrom_of_steps :
    ∀ (events : List (FetchEvent Page)) (cache : ℕ → Finset Page),
      (∀ (i : ℕ) (h : i < events.length),
        events[i].cacheAfter = cache (i + 1) ∧
        events[i].fetched ∈ events[i].cacheAfter ∧
        events[i].cacheAfter \ cache i = {events[i].fetched}) →
      Schedule.ValidTransitionsFrom (cache 0) events := by
  intro events
  induction events with
  | nil => intro _ _; trivial
  | cons event rest ih =>
      intro cache hstep
      obtain ⟨hcache, hmem, hdiff⟩ := hstep 0 (by simp)
      refine ⟨hmem, hdiff, ?_⟩
      rw [show event.cacheAfter = cache 1 from hcache]
      exact ih (fun i => cache (i + 1)) fun i hi => hstep (i + 1) (Nat.succ_lt_succ hi)

/-! ## The replayed queue after each payment

Both remaining structural checks are statements about an arbitrary payment log
that is `FreshPayments`, so they are proved at that generality and only then
specialized to the log of a completed `FIFO.run`. -/

/-- The queue recorded by payment `i` is one FIFO insertion applied to the
replay of the payments before it. -/
private theorem queueAfter_eq_insertPage {capacity : ℕ} {initial : List Page}
    {payments : List (Payment Page)} (hfresh : FreshPayments capacity initial payments)
    (i : ℕ) (hi : i < payments.length) :
    payments[i].queueAfter =
      insertPage capacity (recentPages capacity initial (payments.take i))
        payments[i].page := by
  rw [hfresh.queueAfter_at i hi, List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some]
  exact (recentPages_append capacity initial (payments.take i)
    (recentPages capacity initial (payments.take i)) payments[i] rfl).symm

/-- Erasing a fresh payment log to public fetch events yields a legal
transition sequence from the initial queue: each event adds exactly the page
it fetches. -/
private theorem validTransitionsFrom_map_fetchEvent {capacity : ℕ} {initial : List Page}
    {payments : List (Payment Page)} (hfresh : FreshPayments capacity initial payments) :
    Schedule.ValidTransitionsFrom initial.toFinset (payments.map Payment.fetchEvent) := by
  have hzero : ((recentPages capacity initial (payments.take 0)).toFinset : Finset Page) =
      initial.toFinset := by
    simp [recentPages]
  rw [← hzero]
  refine validTransitionsFrom_of_steps _
    (fun i => (recentPages capacity initial (payments.take i)).toFinset) ?_
  intro i hi
  have hlen : i < payments.length := by simpa using hi
  have hstep := queueAfter_eq_insertPage hfresh i hlen
  simp only [List.getElem_map, Payment.fetchEvent_cacheAfter, Payment.fetchEvent_fetched]
  refine ⟨by rw [hfresh.queueAfter_at i hlen], ?_, ?_⟩ <;> rw [hstep]
  · exact List.mem_toFinset.mpr (mem_insertPage_self _ _ _)
  · exact insertPage_toFinset_sdiff _ _ _ (hfresh.fresh_at i hlen)

/-- A fresh payment log never records a queue exceeding the cache capacity. -/
private theorem queueAfter_toFinset_card_le {capacity : ℕ} (hpositive : 0 < capacity)
    {initial : List Page} (hinitial : initial.length ≤ capacity)
    {payments : List (Payment Page)} (hfresh : FreshPayments capacity initial payments)
    {payment : Payment Page} (hmem : payment ∈ payments) :
    payment.queueAfter.toFinset.card ≤ capacity := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
  calc
    payments[i].queueAfter.toFinset.card ≤ payments[i].queueAfter.length :=
      List.toFinset_card_le _
    _ = min capacity (initial.length + (payments.take (i + 1)).length) := by
        rw [hfresh.queueAfter_at i hi]
        exact recentPages_length capacity hpositive initial hinitial _
    _ ≤ capacity := min_le_left _ _

/-! ## The four feasibility checks -/

/-- The public schedule is exactly the erasure of the final payment log. -/
private theorem schedule_events (input : Instance Page) :
    (schedule trigger input).events =
      (run trigger input (2 * input.requests.length) (initialState input)).payments.map
        Payment.fetchEvent :=
  rfl

private theorem schedule_chronological (input : Instance Page) :
    (schedule trigger input).events.Pairwise fun earlier later =>
      earlier.time ≤ later.time := by
  rw [schedule_events, List.pairwise_map]
  exact final_payment_times_chronological input

private theorem schedule_validTransitions (input : Instance Page) :
    Schedule.ValidTransitionsFrom (schedule trigger input).initialCache
      (schedule trigger input).events := by
  rw [schedule_events]
  exact validTransitionsFrom_map_fetchEvent (final_freshPayments input)

private theorem schedule_capacity (input : Instance Page) :
    ∀ event ∈ (schedule trigger input).events,
      event.cacheAfter.card ≤ input.cacheSize := by
  rw [schedule_events]
  intro event hevent
  obtain ⟨payment, hpayment, rfl⟩ := List.mem_map.mp hevent
  exact queueAfter_toFinset_card_le input.positiveCapacity input.initialCache_full.le
    (final_freshPayments input) hpayment

/-- Every input occurrence is served by the public trace: it is either a cache
hit at its arrival, or it belongs to a payment batch whose time is a service
candidate.  This is the same partition that `FIFO.algorithmCostClaim` uses to
regroup the delay cost. -/
private theorem exists_serviceCandidate (input : Instance Page)
    {occurrence : Occurrence Page} (hinput : occurrence ∈ enumerate input.requests) :
    ((schedule trigger input).serviceCandidates occurrence.request).Nonempty := by
  by_cases hserved : occurrence ∈
      (run trigger input (2 * input.requests.length) (initialState input)).payments.flatMap
        Payment.served
  · obtain ⟨payment, hpayment, hbatch⟩ := List.mem_flatMap.mp hserved
    obtain ⟨hpage, harrival⟩ :=
      History.final_validBatches input payment hpayment
        occurrence hbatch
    exact ⟨payment.time,
      payment_time_mem_serviceCandidates _ _ payment occurrence hpayment harrival hpage⟩
  · have hhit := final_dropped_occurrence_is_hit input occurrence hinput hserved
    exact ⟨occurrence.request.arrival, by
      simp [Schedule.serviceCandidates, hhit]⟩

private theorem schedule_eventuallyServed (input : Instance Page) :
    ∀ request ∈ input.requests,
      ((schedule trigger input).serviceCandidates request).Nonempty := by
  intro request hrequest
  rw [← enumerate_map_request input.requests] at hrequest
  obtain ⟨occurrence, hoccurrence, rfl⟩ := List.mem_map.mp hrequest
  exact exists_serviceCandidate input hoccurrence

/-- **The FIFO schedule is a legal paging solution, for every trigger.** -/
theorem schedule_feasible (trigger : Trigger) (input : Instance Page) :
    (schedule trigger input).Feasible input where
  initialCache := rfl
  chronological := schedule_chronological input
  validTransitions := schedule_validTransitions input
  capacity := schedule_capacity input
  eventuallyServed := schedule_eventuallyServed input
end


end PagingWithDelay.FIFO
