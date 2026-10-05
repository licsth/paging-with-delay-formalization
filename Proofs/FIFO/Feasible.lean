import Proofs.EventLoop.ServiceSemantics

/-!
# Feasibility of the schedule produced by FIFO, for every threshold

The competitive-ratio theorem compares `(FIFO.schedule δ input valid).totalCost`
against every *feasible* comparator.  That statement is only about a legal
paging algorithm if FIFO's own emitted trace is itself feasible, which is what
this file establishes, for *every* threshold `δ : Cost`:

```text
(FIFO.schedule δ input valid).Feasible input
```

Nothing in the argument constrains `δ`: a payment is legal wherever the
threshold happens to be crossed, so feasibility is a fact about the shape of
the event loop, not about the amount of delay it tolerates.

Nothing here is new mathematics.  Each of the five checks in
`Schedule.Feasible` is discharged from an invariant that the competitive proof
already had to establish about `FIFO.run`:

| field | source |
| --- | --- |
| `initialCache` | the queue starts as `input.initialCache` (`schedule` records it) |
| `chronological` | `FIFO.final_payment_times_chronological` |
| `validTransitions` | `FreshPayments`: a payment page is absent from the replayed queue |
| `capacity` | `recentPages_length`, via `FreshPayments.queueAfter_at` |
| `eventuallyServed` | the hit/batch partition also used by `FIFO.algorithmCostClaim` |

The point of the file is to let a reader check the model rather than trust it.
`Schedule.Feasible` is otherwise only ever used as a hypothesis on the
comparator, so without this theorem the paper-facing bound would constrain a
cost expression without asserting that the trace it is computed from is an
admissible paging solution.
-/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page] {δ : Cost}

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
  simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_singleton]
  unfold insertPage
  split
  · simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨hold | hnew, hnot⟩
      · exact False.elim (hnot hold)
      · exact hnew
    · rintro rfl
      exact ⟨Or.inr rfl, hpage⟩
  · simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨hold | hnew, hnot⟩
      · exact False.elim (hnot (List.mem_of_mem_tail hold))
      · exact hnew
    · rintro rfl
      exact ⟨Or.inr rfl, hpage⟩

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
      have head := hstep 0 (by simp)
      have hcache : event.cacheAfter = cache 1 := head.1
      have hmem : event.fetched ∈ event.cacheAfter := head.2.1
      have hdiff : event.cacheAfter \ cache 0 = {event.fetched} := head.2.2
      refine ⟨hmem, hdiff, ?_⟩
      rw [hcache]
      refine ih (fun i => cache (i + 1)) ?_
      intro i hi
      exact hstep (i + 1) (Nat.succ_lt_succ hi)

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
  have hmiss : payments[i].page ∉ recentPages capacity initial (payments.take i) :=
    hfresh.fresh_at i hlen
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [List.getElem_map, Payment.fetchEvent_cacheAfter,
      Payment.fetchEvent_fetched]
  · rw [hfresh.queueAfter_at i hlen]
  · rw [List.mem_toFinset, hstep]
    exact mem_insertPage_self _ _ _
  · rw [hstep]
    exact insertPage_toFinset_sdiff _ _ _ hmiss

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
private theorem schedule_events (input : Instance Page) (valid : input.Valid) :
    (schedule δ input valid).events =
      (run δ input (2 * input.requests.length) (initialState input)).payments.map
        Payment.fetchEvent :=
  rfl

private theorem schedule_chronological (input : Instance Page) (valid : input.Valid) :
    (schedule δ input valid).events.Pairwise fun earlier later =>
      earlier.time ≤ later.time := by
  rw [schedule_events, List.pairwise_map]
  exact final_payment_times_chronological input valid

private theorem schedule_validTransitions (input : Instance Page) (valid : input.Valid) :
    Schedule.ValidTransitionsFrom (schedule δ input valid).initialCache
      (schedule δ input valid).events := by
  rw [schedule_events]
  exact validTransitionsFrom_map_fetchEvent (final_freshPayments input valid)

private theorem schedule_capacity (input : Instance Page) (valid : input.Valid) :
    ∀ event ∈ (schedule δ input valid).events,
      event.cacheAfter.card ≤ input.cacheSize := by
  rw [schedule_events]
  intro event hevent
  obtain ⟨payment, hpayment, rfl⟩ := List.mem_map.mp hevent
  exact queueAfter_toFinset_card_le valid.positiveCapacity valid.initialCache_full.le
    (final_freshPayments input valid) hpayment

/-- Every input occurrence is served by the public trace: it is either a cache
hit at its arrival, or it belongs to a payment batch whose time is a service
candidate.  This is the same partition that `FIFO.algorithmCostClaim` uses to
regroup the delay cost. -/
private theorem exists_serviceCandidate (input : Instance Page) (valid : input.Valid)
    {occurrence : Occurrence Page} (hinput : occurrence ∈ enumerate input.requests) :
    ((schedule δ input valid).serviceCandidates occurrence.request).Nonempty := by
  by_cases hserved : occurrence ∈
      (run δ input (2 * input.requests.length) (initialState input)).payments.flatMap
        Payment.served
  · obtain ⟨payment, hpayment, hbatch⟩ := List.mem_flatMap.mp hserved
    obtain ⟨hpage, harrival⟩ :=
      History.final_validBatches input valid payment hpayment
        occurrence hbatch
    exact ⟨payment.time,
      payment_time_mem_serviceCandidates _ _ payment occurrence hpayment harrival hpage⟩
  · have hhit := final_dropped_occurrence_is_hit input valid occurrence hinput hserved
    exact ⟨occurrence.request.arrival, by
      simp [Schedule.serviceCandidates, hhit]⟩

private theorem schedule_eventuallyServed (input : Instance Page) (valid : input.Valid) :
    ∀ request ∈ input.requests,
      ((schedule δ input valid).serviceCandidates request).Nonempty := by
  intro request hrequest
  rw [← enumerate_map_request input.requests] at hrequest
  obtain ⟨occurrence, hoccurrence, rfl⟩ := List.mem_map.mp hrequest
  exact exists_serviceCandidate input valid hoccurrence

/-- **The FIFO schedule is a legal paging solution, for every threshold `δ`.**
Together with `RankPotential.competitiveRatio` at `δ = 1` this upgrades the
paper-facing bound from a statement about a cost expression to a statement
about an algorithm. -/
theorem schedule_feasible (δ : Cost) (input : Instance Page) (valid : input.Valid) :
    (schedule δ input valid).Feasible input where
  initialCache := rfl
  chronological := schedule_chronological input valid
  validTransitions := schedule_validTransitions input valid
  capacity := schedule_capacity input valid
  eventuallyServed := schedule_eventuallyServed input valid

theorem feasible (δ : Cost): Algorithm.Feasible (FIFO.schedule δ (Page := Page)) where
  scheduleFeasible := schedule_feasible δ

end


end PagingWithDelay.FIFO
