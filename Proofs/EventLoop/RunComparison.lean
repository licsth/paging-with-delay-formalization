import Proofs.EventLoop.PaymentOrder
import Proofs.EventLoop.ServiceBridge

/-!
# Comparing two runs of the FIFO event loop

The proof that FIFO is online (`Proofs/FIFO/Online.lean`) and the proof
that it is nonclairvoyant (`Proofs/FIFO/Nonclairvoyant.lean`) both
compare the run of the event loop on one instance with its run on another that
tells the algorithm the same story up to a time `t`.  This file collects what
the two proofs share, and what neither of them is really about.

* **Fuel.**  `FIFO.run` recurses on `2 * requests.length`, which changes with
  the request list.  `run_eq_of_le` shows that fuel beyond the point where
  `nextAction?` returns `none` is inert, so two runs can be given a common
  budget.
* **The instance.**  `step` reads its `Instance` argument only through
  `cacheSize`, so `run_congr` turns runs of two instances of equal capacity
  into runs of the same one.
* **Events at or before `t`.**  `earlyPayments` is the part of the payment log
  the public schedule shows at or before `t`.  `late_payments` and
  `no_early_payments` are the two reasons a run adds nothing further to it.
* **Truncation.**  Chronology makes `filter (arrival ≤ t)` a prefix of the
  request list, and prefixes commute with `enumerate` and with the erasure of
  the payment log.
-/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page] {trigger : Trigger}

noncomputable section

/-- The payments that the public schedule shows at or before time `t`. -/
def earlyPayments (t : Time) (state : State Page) : List (Payment Page) :=
  state.payments.filter fun payment => decide (payment.time ≤ t)

/-! ## Fuel beyond termination is inert -/

theorem run_succ_eq_of_finished (input : Instance Page) :
    ∀ (fuel : ℕ) (state : State Page), nextAction? trigger (run trigger input fuel state) = none →
      run trigger input (fuel + 1) state = run trigger input fuel state := by
  intro fuel
  induction fuel with
  | zero =>
      intro state hfinished
      simp only [run] at hfinished ⊢
      rw [hfinished]
  | succ fuel ih =>
      intro state hfinished
      cases haction : nextAction? trigger state with
      | none => simp [run, haction]
      | some action =>
          simp only [run, haction] at hfinished ⊢
          exact ih _ hfinished

/-- Any two fuel budgets that both suffice give the same final state. -/
theorem run_eq_of_le (input : Instance Page) (state : State Page) {fuel larger : ℕ}
    (hfuel : potential state ≤ fuel) (hle : fuel ≤ larger) :
    run trigger input larger state = run trigger input fuel state := by
  induction larger with
  | zero =>
      have : fuel = 0 := Nat.le_zero.mp hle
      rw [this]
  | succ larger ih =>
      rcases Nat.lt_or_ge larger fuel with hlt | hge
      · have : fuel = larger + 1 := by omega
        rw [this]
      · have hsmaller : run trigger input larger state = run trigger input fuel state := ih hge
        have hfinished : nextAction? trigger (run trigger input larger state) = none := by
          rw [hsmaller]
          exact run_finished_of_potential_le input state fuel hfuel
        rw [run_succ_eq_of_finished input larger state hfinished, hsmaller]

/-! ## The event loop reads only the cache capacity of its instance -/

theorem step_congr {first second : Instance Page}
    (hcache : first.cacheSize = second.cacheSize) (state : State Page)
    (action : Action Page) : step first state action = step second state action := by
  cases action with
  | arrival occurrence => rfl
  | payment time page => simp only [step, hcache]

/-- Two instances with the same cache capacity drive the event loop
identically.  Everything else about an instance is only used to build the
initial state. -/
theorem run_congr {first second : Instance Page}
    (hcache : first.cacheSize = second.cacheSize) :
    ∀ (fuel : ℕ) (state : State Page), run trigger first fuel state = run trigger second fuel state := by
  intro fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel ih =>
      intro state
      cases haction : nextAction? trigger state with
      | none => simp [run, haction]
      | some action =>
          simp only [run, haction]
          rw [step_congr hcache]
          exact ih _

theorem arrival_mem_unseen {state : State Page} {occurrence : Occurrence Page}
    (haction : nextAction? trigger state = some (.arrival occurrence)) :
    occurrence ∈ state.unseen := by
  unfold nextAction? at haction
  cases hunseen : state.unseen with
  | nil => cases hpayment : nextPayment? trigger state <;> simp [hunseen, hpayment] at haction
  | cons head tail =>
      cases hpayment : nextPayment? trigger state with
      | none =>
          simp only [hunseen, hpayment] at haction
          injection haction with heq
          cases heq
          simp
      | some pair =>
          simp only [hunseen, hpayment] at haction
          split at haction
          · injection haction with heq
            cases heq
            simp
          · simp at haction

/-! ## After time `t` has passed, no further event is early -/

/-- Once the event loop's clock is past `t`, no payment it still makes can land
at or before `t`. -/
theorem late_payments (input : Instance Page) (t : Time) :
    ∀ (fuel : ℕ) (state : State Page), TimeInvariant state → t < state.now →
      earlyPayments t (run trigger input fuel state) = earlyPayments t state := by
  intro fuel
  induction fuel with
  | zero => intro state _ _; rfl
  | succ fuel ih =>
      intro state htime hnow
      cases haction : nextAction? trigger state with
      | none => simp [run, haction]
      | some action =>
          simp only [run, haction]
          have hstep := step_timeInvariant input state action htime haction
          cases action with
          | arrival occurrence =>
              have hlater : state.now ≤ occurrence.request.arrival :=
                htime.now_before_unseen occurrence (arrival_mem_unseen haction)
              rw [ih _ hstep (hnow.trans_le hlater)]
              rfl
          | payment time page =>
              have hselected := nextAction_payment_selected haction
              have hpending := pending_of_mem_pendingPages
                (nextPayment_mem_pendingPages hselected)
              have hge : state.now ≤ time := by
                rw [← nextPayment_time_eq hselected]
                exact trigger.dueTime_ge_now state page hpending
              have hlate : t < time := hnow.trans_le hge
              rw [ih _ hstep hlate]
              simp [earlyPayments, step, not_le_of_gt hlate]

/-- If every request still to arrive comes after `t`, and no payment is due at
or before `t`, then the run contributes no further early payment. -/
theorem no_early_payments (input : Instance Page) (t : Time) (fuel : ℕ)
    (state : State Page) (htime : TimeInvariant state)
    (hunseen : ∀ occurrence ∈ state.unseen, t < occurrence.request.arrival)
    (hdue : ∀ time page, nextPayment? trigger state = some (time, page) → t < time) :
    earlyPayments t (run trigger input fuel state) = earlyPayments t state := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases haction : nextAction? trigger state with
      | none => simp [run, haction]
      | some action =>
          simp only [run, haction]
          have hstep := step_timeInvariant input state action htime haction
          cases action with
          | arrival occurrence =>
              have hlate : t < occurrence.request.arrival :=
                hunseen occurrence (arrival_mem_unseen haction)
              rw [late_payments input t fuel _ hstep (by simpa [step] using hlate)]
              rfl
          | payment time page =>
              have hlate : t < time := hdue time page (nextAction_payment_selected haction)
              rw [late_payments input t fuel _ hstep (by simpa [step] using hlate)]
              simp [earlyPayments, step, not_le_of_gt hlate]

/-! ## With no arrival left, a payment due by `t` is forced -/

/-- With no arrival left before `t`, a payment due at or before `t` is the
action both states must take. -/
theorem nextAction_payment_of_late_unseen {state : State Page} {t time : Time}
    {page : Page} (hselected : nextPayment? trigger state = some (time, page))
    (hunseen : ∀ occurrence ∈ state.unseen, t < occurrence.request.arrival)
    (hdue : time ≤ t) : nextAction? trigger state = some (.payment time page) := by
  cases hcases : state.unseen with
  | nil => simp [nextAction?, hcases, hselected]
  | cons head tail =>
      have hlate : t < head.request.arrival := by
        apply hunseen
        rw [hcases]
        simp
      have hnot : ¬ head.request.arrival ≤ time := by
        intro hle
        exact absurd (hle.trans hdue) (not_le_of_gt hlate)
      simp [nextAction?, hcases, hselected, hnot]

/-! ## A chronological request list is truncated by taking a prefix -/

omit [DecidableEq Page] in
theorem filter_eq_take_of_chronological {requests : List (Request Page)}
    (hchronological : requests.Pairwise fun earlier later => earlier.arrival ≤ later.arrival)
    (t : Time) :
    ∃ count, requests.filter (fun request => decide (request.arrival ≤ t)) =
        requests.take count ∧
      ∀ request ∈ requests.drop count, t < request.arrival := by
  induction requests with
  | nil => exact ⟨0, rfl, by simp⟩
  | cons request rest ih =>
      rw [List.pairwise_cons] at hchronological
      by_cases harrival : request.arrival ≤ t
      · obtain ⟨count, hfilter, hdrop⟩ := ih hchronological.2
        exact ⟨count + 1, by simp [harrival, hfilter], by simpa using hdrop⟩
      · have hlate : ∀ later ∈ request :: rest, t < later.arrival := by
          intro later hlater
          rcases List.mem_cons.mp hlater with rfl | hlater
          · exact lt_of_not_ge harrival
          · exact (lt_of_not_ge harrival).trans_le (hchronological.1 later hlater)
        refine ⟨0, ?_, by simpa using hlate⟩
        simp only [List.take_zero]
        exact List.filter_eq_nil_iff.mpr fun later hlater => by
          simpa using not_le_of_gt (hlate later hlater)

/-! ## Enumeration commutes with truncation -/

omit [DecidableEq Page] in
theorem enumerateFrom_take (start count : ℕ) (requests : List (Request Page)) :
    enumerateFrom start (requests.take count) = (enumerateFrom start requests).take count := by
  induction requests generalizing start count with
  | nil => simp [enumerateFrom]
  | cons request rest ih =>
      cases count with
      | zero => simp [enumerateFrom]
      | succ count => simp [enumerateFrom, ih]

omit [DecidableEq Page] in
theorem mem_enumerateFrom_request {start : ℕ} {requests : List (Request Page)}
    {occurrence : Occurrence Page} (hmem : occurrence ∈ enumerateFrom start requests) :
    occurrence.request ∈ requests := by
  rw [← enumerateFrom_map_request start requests]
  exact List.mem_map_of_mem hmem

omit [DecidableEq Page] in
theorem enumerateFrom_drop_eq (start count : ℕ) (requests : List (Request Page)) :
    (enumerateFrom start requests).drop count =
      enumerateFrom (start + count) (requests.drop count) := by
  induction requests generalizing start count with
  | nil => simp [enumerateFrom]
  | cons request rest ih =>
      cases count with
      | zero => simp [enumerateFrom]
      | succ count =>
          simp only [enumerateFrom, List.drop_succ_cons, ih]
          congr 1
          omega

/-! ## Erasing the payment log commutes with truncation -/

theorem filter_map_fetchEvent (t : Time) (payments : List (Payment Page)) :
    (payments.map Payment.fetchEvent).filter (fun event => decide (event.time ≤ t)) =
      (payments.filter fun payment => decide (payment.time ≤ t)).map Payment.fetchEvent := by
  induction payments with
  | nil => rfl
  | cons payment rest ih =>
      by_cases htime : payment.time ≤ t <;> simp [htime, ih]

theorem schedule_events (input : Instance Page) :
    (schedule trigger input).events =
      (run trigger input (2 * input.requests.length) (initialState input)).payments.map
        Payment.fetchEvent :=
  rfl

theorem potential_initialState (input : Instance Page) :
    potential (initialState input) = 2 * input.requests.length := by
  have hlength : ∀ (start : ℕ) (requests : List (Request Page)),
      (enumerateFrom start requests).length = requests.length := by
    intro start requests
    induction requests generalizing start with
    | nil => rfl
    | cons request rest ih => simp [enumerateFrom, ih]
  simp [potential, initialState, enumerate, hlength]

end
end PagingWithDelay.FIFO
