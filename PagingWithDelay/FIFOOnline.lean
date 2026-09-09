import PagingWithDelay.Online
import PagingWithDelay.EventLoop.PaymentOrder
import PagingWithDelay.EventLoop.ServiceBridge

/-!
# FIFO is online, for every threshold

This file proves `Algorithm.Online (FIFO.schedule δ)` for every threshold
`δ : Cost`: what the algorithm does up to a time `t` depends only on the
requests that have arrived by `t`.  The threshold is a parameter throughout;
the simulation below never inspects it, it only needs both runs to use the
same one.

## Strategy

By `Algorithm.online_iff_upTo_eq` it is enough to compare an instance with its
own truncation, so the whole development is about a single request list.  Three
obstacles have to be removed.

* **Different fuel.**  `FIFO.run` recurses on `2 * requests.length`, which
  shrinks under truncation.  `run_eq_of_le` shows that fuel beyond the point
  where `nextAction?` returns `none` is inert, so both sides can be run with a
  common fuel.
* **Different instances.**  `step` reads its `Instance` argument only through
  `cacheSize`, so `run_congr` turns the two runs into runs of the *same* input
  that differ only in their initial `unseen` list.
* **Different `unseen` lists.**  `Instance.Chronological` makes
  `filter (arrival ≤ t)` a *prefix* of the request list
  (`filter_eq_take_of_chronological`), so the two lists share a prefix and every
  occurrence past it arrives strictly after `t`.

What remains is the simulation `Mirror`: two states with equal `now`, `queue`,
`pending` and `payments` whose `unseen` lists share a prefix.  While the shared
prefix is being consumed both states select the same action, because
`nextPayment?` reads only `now` and `pending`.  Once it is exhausted, either a
payment is still due at a time `≤ t` — and then both states must take it,
since every remaining arrival is later than `t` — or no payment is due by `t`,
and `no_early_payments` shows neither run contributes another event before `t`.
-/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page] {δ : Cost}

noncomputable section

/-- The payments that the public schedule shows at or before time `t`. -/
private def earlyPayments (t : Time) (state : State Page) : List (Payment Page) :=
  state.payments.filter fun payment => decide (payment.time ≤ t)

/-! ## Fuel beyond termination is inert -/

private theorem run_succ_eq_of_finished (input : Instance Page) :
    ∀ (fuel : ℕ) (state : State Page), nextAction? δ (run δ input fuel state) = none →
      run δ input (fuel + 1) state = run δ input fuel state := by
  intro fuel
  induction fuel with
  | zero =>
      intro state hfinished
      simp only [run] at hfinished ⊢
      rw [hfinished]
  | succ fuel ih =>
      intro state hfinished
      cases haction : nextAction? δ state with
      | none => simp [run, haction]
      | some action =>
          simp only [run, haction] at hfinished ⊢
          exact ih _ hfinished

/-- Any two fuel budgets that both suffice give the same final state. -/
theorem run_eq_of_le (input : Instance Page) (state : State Page) {fuel larger : ℕ}
    (hfuel : potential state ≤ fuel) (hle : fuel ≤ larger) :
    run δ input larger state = run δ input fuel state := by
  induction larger with
  | zero =>
      have : fuel = 0 := Nat.le_zero.mp hle
      rw [this]
  | succ larger ih =>
      rcases Nat.lt_or_ge larger fuel with hlt | hge
      · have : fuel = larger + 1 := by omega
        rw [this]
      · have hsmaller : run δ input larger state = run δ input fuel state := ih hge
        have hfinished : nextAction? δ (run δ input larger state) = none := by
          rw [hsmaller]
          exact run_finished_of_potential_le input state fuel hfuel
        rw [run_succ_eq_of_finished input larger state hfinished, hsmaller]

/-! ## The event loop reads only the cache capacity of its instance -/

private theorem step_congr {first second : Instance Page}
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
    ∀ (fuel : ℕ) (state : State Page), run δ first fuel state = run δ second fuel state := by
  intro fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel ih =>
      intro state
      cases haction : nextAction? δ state with
      | none => simp [run, haction]
      | some action =>
          simp only [run, haction]
          rw [step_congr hcache]
          exact ih _

/-! ## Selection depends only on `now` and `pending` -/

private theorem pendingCost_congr {s₁ s₂ : State Page} (hpending : s₁.pending = s₂.pending) :
    pendingCost s₁ = pendingCost s₂ := by
  funext page instant
  simp only [pendingCost, hpending]

private theorem thresholdTime_congr {s₁ s₂ : State Page} (hnow : s₁.now = s₂.now)
    (hpending : s₁.pending = s₂.pending) : thresholdTime δ s₁ = thresholdTime δ s₂ := by
  funext page
  simp only [thresholdTime, hnow, pendingCost_congr hpending]

private theorem nextPayment?_congr {s₁ s₂ : State Page} (hnow : s₁.now = s₂.now)
    (hpending : s₁.pending = s₂.pending) : nextPayment? δ s₁ = nextPayment? δ s₂ := by
  simp only [nextPayment?, pendingPages, hpending, thresholdTime_congr hnow hpending]

private theorem nextAction?_congr {s₁ s₂ : State Page}
    (hhead : s₁.unseen.head? = s₂.unseen.head?)
    (hpayment : nextPayment? δ s₁ = nextPayment? δ s₂) : nextAction? δ s₁ = nextAction? δ s₂ := by
  cases h₁ : s₁.unseen with
  | nil =>
      cases h₂ : s₂.unseen with
      | nil => simp [nextAction?, h₁, h₂, hpayment]
      | cons second rest => rw [h₁, h₂] at hhead; simp at hhead
  | cons first rest₁ =>
      cases h₂ : s₂.unseen with
      | nil => rw [h₁, h₂] at hhead; simp at hhead
      | cons second rest₂ =>
          have hfirst : first = second := by
            rw [h₁, h₂] at hhead
            simpa using hhead
          subst hfirst
          cases hpair : nextPayment? δ s₂ with
          | none => simp [nextAction?, h₁, h₂, hpayment, hpair]
          | some pair =>
              obtain ⟨time, page⟩ := pair
              simp [nextAction?, h₁, h₂, hpayment, hpair]

private theorem arrival_mem_unseen {state : State Page} {occurrence : Occurrence Page}
    (haction : nextAction? δ state = some (.arrival occurrence)) :
    occurrence ∈ state.unseen := by
  unfold nextAction? at haction
  cases hunseen : state.unseen with
  | nil => cases hpayment : nextPayment? δ state <;> simp [hunseen, hpayment] at haction
  | cons head tail =>
      cases hpayment : nextPayment? δ state with
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
private theorem late_payments (input : Instance Page) (t : Time) :
    ∀ (fuel : ℕ) (state : State Page), TimeInvariant state → t < state.now →
      earlyPayments t (run δ input fuel state) = earlyPayments t state := by
  intro fuel
  induction fuel with
  | zero => intro state _ _; rfl
  | succ fuel ih =>
      intro state htime hnow
      cases haction : nextAction? δ state with
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
                exact thresholdTime_ge_now state page hpending
              have hlate : t < time := hnow.trans_le hge
              rw [ih _ hstep hlate]
              simp [earlyPayments, step, not_le_of_gt hlate]

/-- If every request still to arrive comes after `t`, and no payment is due at
or before `t`, then the run contributes no further early payment. -/
private theorem no_early_payments (input : Instance Page) (t : Time) (fuel : ℕ)
    (state : State Page) (htime : TimeInvariant state)
    (hunseen : ∀ occurrence ∈ state.unseen, t < occurrence.request.arrival)
    (hdue : ∀ time page, nextPayment? δ state = some (time, page) → t < time) :
    earlyPayments t (run δ input fuel state) = earlyPayments t state := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases haction : nextAction? δ state with
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

/-! ## The simulation -/

/-- Two event-loop states that agree on everything except a suffix of not-yet
arrived requests, all of which arrive after `t`. -/
private structure Mirror (t : Time) (s₁ s₂ : State Page) : Prop where
  now_eq : s₁.now = s₂.now
  queue_eq : s₁.queue = s₂.queue
  pending_eq : s₁.pending = s₂.pending
  payments_eq : s₁.payments = s₂.payments
  unseen_split : ∃ shared rest₁ rest₂,
    s₁.unseen = shared ++ rest₁ ∧ s₂.unseen = shared ++ rest₂ ∧
      (∀ occurrence ∈ rest₁, t < occurrence.request.arrival) ∧
      (∀ occurrence ∈ rest₂, t < occurrence.request.arrival)

private theorem Mirror.step (input : Instance Page) {t : Time} {s₁ s₂ : State Page}
    (mirror : Mirror t s₁ s₂) (action : Action Page) :
    Mirror t (FIFO.step input s₁ action) (FIFO.step input s₂ action) := by
  obtain ⟨shared, rest₁, rest₂, h₁, h₂, hrest₁, hrest₂⟩ := mirror.unseen_split
  cases action with
  | arrival occurrence =>
      refine ⟨rfl, mirror.queue_eq, ?_, mirror.payments_eq, ?_⟩
      · simp only [FIFO.step, mirror.queue_eq, mirror.pending_eq]
      · cases shared with
        | nil =>
            exact ⟨[], rest₁.tail, rest₂.tail, by simp [FIFO.step, h₁],
              by simp [FIFO.step, h₂],
              fun o ho => hrest₁ o (List.mem_of_mem_tail ho),
              fun o ho => hrest₂ o (List.mem_of_mem_tail ho)⟩
        | cons head tail =>
            exact ⟨tail, rest₁, rest₂, by simp [FIFO.step, h₁], by simp [FIFO.step, h₂],
              hrest₁, hrest₂⟩
  | payment time page =>
      refine ⟨rfl, ?_, ?_, ?_, ⟨shared, rest₁, rest₂, by simpa [FIFO.step] using h₁,
        by simpa [FIFO.step] using h₂, hrest₁, hrest₂⟩⟩
      · simp only [FIFO.step, mirror.queue_eq]
      · simp only [FIFO.step, mirror.pending_eq]
      · simp only [FIFO.step, mirror.pending_eq, mirror.payments_eq, mirror.queue_eq]

/-- With no arrival left before `t`, a payment due at or before `t` is the
action both states must take. -/
private theorem nextAction_payment_of_late_unseen {state : State Page} {t time : Time}
    {page : Page} (hselected : nextPayment? δ state = some (time, page))
    (hunseen : ∀ occurrence ∈ state.unseen, t < occurrence.request.arrival)
    (hdue : time ≤ t) : nextAction? δ state = some (.payment time page) := by
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

private theorem mirror_earlyPayments (input : Instance Page) (t : Time) :
    ∀ (fuel : ℕ) (s₁ s₂ : State Page), TimeInvariant s₁ → TimeInvariant s₂ →
      Mirror t s₁ s₂ →
      earlyPayments t (run δ input fuel s₁) = earlyPayments t (run δ input fuel s₂) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s₁ s₂ _ _ mirror
      simp [run, earlyPayments, mirror.payments_eq]
  | succ fuel ih =>
      intro s₁ s₂ htime₁ htime₂ mirror
      obtain ⟨shared, rest₁, rest₂, h₁, h₂, hrest₁, hrest₂⟩ := mirror.unseen_split
      have hpayment : nextPayment? δ s₁ = nextPayment? δ s₂ :=
        nextPayment?_congr mirror.now_eq mirror.pending_eq
      have advance : ∀ action, nextAction? δ s₁ = some action → nextAction? δ s₂ = some action →
          earlyPayments t (run δ input (fuel + 1) s₁) =
            earlyPayments t (run δ input (fuel + 1) s₂) := by
        intro action ha₁ ha₂
        simp only [run, ha₁, ha₂]
        exact ih _ _ (step_timeInvariant input s₁ action htime₁ ha₁)
          (step_timeInvariant input s₂ action htime₂ ha₂) (mirror.step input action)
      cases shared with
      | cons head tail =>
          have hhead : s₁.unseen.head? = s₂.unseen.head? := by simp [h₁, h₂]
          have haction : nextAction? δ s₁ = nextAction? δ s₂ := nextAction?_congr hhead hpayment
          cases ha₁ : nextAction? δ s₁ with
          | none =>
              have ha₂ : nextAction? δ s₂ = none := by rw [← haction, ha₁]
              simp [run, ha₁, ha₂, earlyPayments, mirror.payments_eq]
          | some action =>
              exact advance action ha₁ (by rw [← haction, ha₁])
      | nil =>
          simp only [List.nil_append] at h₁ h₂
          have hunseen₁ : ∀ occurrence ∈ s₁.unseen, t < occurrence.request.arrival := by
            rw [h₁]; exact hrest₁
          have hunseen₂ : ∀ occurrence ∈ s₂.unseen, t < occurrence.request.arrival := by
            rw [h₂]; exact hrest₂
          by_cases hdue : ∃ time page, nextPayment? δ s₁ = some (time, page) ∧ time ≤ t
          · obtain ⟨time, page, hselected, hle⟩ := hdue
            refine advance (.payment time page)
              (nextAction_payment_of_late_unseen hselected hunseen₁ hle)
              (nextAction_payment_of_late_unseen (hpayment ▸ hselected) hunseen₂ hle)
          · push_neg at hdue
            have hlate₁ : ∀ time page, nextPayment? δ s₁ = some (time, page) → t < time :=
              hdue
            have hlate₂ : ∀ time page, nextPayment? δ s₂ = some (time, page) → t < time := by
              intro time page hselected
              exact hlate₁ time page (by rw [hpayment]; exact hselected)
            rw [no_early_payments input t _ s₁ htime₁ hunseen₁ hlate₁,
              no_early_payments input t _ s₂ htime₂ hunseen₂ hlate₂]
            simp [earlyPayments, mirror.payments_eq]

/-! ## A chronological request list is truncated by taking a prefix -/

omit [DecidableEq Page] in
private theorem filter_eq_take_of_chronological {requests : List (Request Page)}
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
private theorem enumerateFrom_take (start count : ℕ) (requests : List (Request Page)) :
    enumerateFrom start (requests.take count) = (enumerateFrom start requests).take count := by
  induction requests generalizing start count with
  | nil => simp [enumerateFrom]
  | cons request rest ih =>
      cases count with
      | zero => simp [enumerateFrom]
      | succ count => simp [enumerateFrom, ih]

omit [DecidableEq Page] in
private theorem mem_enumerateFrom_request {start : ℕ} {requests : List (Request Page)}
    {occurrence : Occurrence Page} (hmem : occurrence ∈ enumerateFrom start requests) :
    occurrence.request ∈ requests := by
  rw [← enumerateFrom_map_request start requests]
  exact List.mem_map_of_mem hmem

omit [DecidableEq Page] in
private theorem enumerateFrom_drop_eq (start count : ℕ) (requests : List (Request Page)) :
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

private theorem filter_map_fetchEvent (t : Time) (payments : List (Payment Page)) :
    (payments.map Payment.fetchEvent).filter (fun event => decide (event.time ≤ t)) =
      (payments.filter fun payment => decide (payment.time ≤ t)).map Payment.fetchEvent := by
  induction payments with
  | nil => rfl
  | cons payment rest ih =>
      by_cases htime : payment.time ≤ t <;> simp [htime, ih]

private theorem schedule_events (input : Instance Page) (valid : input.Valid) :
    (schedule δ input valid).events =
      (run δ input (2 * input.requests.length) (initialState input)).payments.map
        Payment.fetchEvent :=
  rfl

private theorem potential_initialState (input : Instance Page) :
    potential (initialState input) = 2 * input.requests.length := by
  have hlength : ∀ (start : ℕ) (requests : List (Request Page)),
      (enumerateFrom start requests).length = requests.length := by
    intro start requests
    induction requests generalizing start with
    | nil => rfl
    | cons request rest ih => simp [enumerateFrom, ih]
  simp [potential, initialState, enumerate, hlength]

/-! ## The main statement -/

/-- FIFO's behaviour before time `t` is what it would have been on the request
sequence truncated at `t`. -/
theorem schedule_upTo_eq (input : Instance Page) (valid : input.Valid) (t : Time)
    (validUpTo : (input.upTo t).Valid) :
    (schedule δ input valid).upTo t = (schedule δ (input.upTo t) validUpTo).upTo t := by
  obtain ⟨count, hfilter, hdrop⟩ :=
    filter_eq_take_of_chronological (requests := input.requests) valid.chronological t
  have htruncated : (input.upTo t).requests = input.requests.take count := hfilter
  have hcache : (input.upTo t).cacheSize = input.cacheSize := rfl
  -- Raise the truncated run to the fuel of the full run, then reinterpret it
  -- over `input`, which is legitimate because only the capacity is read.
  have hsmall : potential (initialState (input.upTo t)) ≤
      2 * (input.upTo t).requests.length := le_of_eq (potential_initialState _)
  have hle : 2 * (input.upTo t).requests.length ≤ 2 * input.requests.length := by
    have hlen : (input.upTo t).requests.length ≤ input.requests.length := by
      rw [htruncated, List.length_take]
      exact Nat.min_le_right _ _
    omega
  have hraise : run δ (input.upTo t) (2 * (input.upTo t).requests.length)
        (initialState (input.upTo t)) =
      run δ input (2 * input.requests.length) (initialState (input.upTo t)) := by
    rw [← run_eq_of_le (input.upTo t) (initialState (input.upTo t)) hsmall hle]
    exact run_congr hcache _ _
  -- The two initial states mirror each other: chronology makes the truncated
  -- request list a prefix, and everything beyond it arrives after `t`.
  have hmirror : Mirror t (initialState input) (initialState (input.upTo t)) := by
    refine ⟨rfl, rfl, rfl, rfl, ⟨enumerate (input.requests.take count),
      (enumerate input.requests).drop count, [], ?_, ?_, ?_, by simp⟩⟩
    · show enumerate input.requests = _
      simp only [enumerate]
      rw [enumerateFrom_take]
      exact (List.take_append_drop count (enumerateFrom 0 input.requests)).symm
    · show enumerate (input.upTo t).requests = _
      rw [htruncated, List.append_nil]
    · intro occurrence hoccurrence
      simp only [enumerate, enumerateFrom_drop_eq] at hoccurrence
      exact hdrop occurrence.request (mem_enumerateFrom_request hoccurrence)
  have hpayments := mirror_earlyPayments (δ := δ) input t (2 * input.requests.length)
    (initialState input) (initialState (input.upTo t))
    (initial_timeInvariant input valid) (initial_timeInvariant (input.upTo t) validUpTo)
    hmirror
  unfold earlyPayments at hpayments
  unfold Schedule.upTo
  apply congrArg Schedule.mk
  rw [schedule_events, schedule_events, filter_map_fetchEvent, filter_map_fetchEvent,
    hraise]
  exact congrArg (List.map Payment.fetchEvent) hpayments

/-- **FIFO with any threshold `δ` is an online algorithm.** -/
theorem schedule_online (δ : Cost) : Algorithm.Online (FIFO.schedule δ (Page := Page)) :=
  Algorithm.online_of_upTo_eq fun input valid t validUpTo =>
    schedule_upTo_eq input valid t validUpTo

end
end PagingWithDelay.FIFO
