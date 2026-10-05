import Proofs.Basic.Online
import Proofs.EventLoop.RunComparison
import Algorithm

/-!
# FIFO is online, for every trigger

This file proves that FIFO is online for every trigger, threshold or
deadline: what the algorithm does up to a time `t` depends only on the
requests that have arrived by `t`.  The trigger is a parameter throughout;
the simulation below never inspects it, it only needs both runs to use the
same one.

## Strategy

By `Algorithm.online_iff_upTo_eq` it is enough to compare an instance with its
own truncation, so the whole development is about a single request list.  Three
obstacles have to be removed, all three in
`Proofs/EventLoop/RunComparison.lean`.

* **Different fuel.**  `FIFO.run` recurses on `2 * requests.length`, which
  shrinks under truncation.  `run_eq_of_le` shows that fuel beyond the point
  where `nextAction?` returns `none` is inert, so both sides can be run with a
  common fuel.
* **Different instances.**  `step` reads its `Instance` argument only through
  `cacheSize`, so `run_congr` turns the two runs into runs of the *same* input
  that differ only in their initial `unseen` list.
* **Different `unseen` lists.**  `Instance.chronological` makes
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

variable {Page : Type*} [DecidableEq Page] {trigger : Trigger}

noncomputable section

/-! ## Selection depends only on `now` and `pending` -/

private theorem pendingCost_congr {s₁ s₂ : State Page} (hpending : s₁.pending = s₂.pending) :
    pendingCost s₁ = pendingCost s₂ := by
  funext page instant
  simp only [pendingCost, hpending]

private theorem dueTime_congr {s₁ s₂ : State Page} (hnow : s₁.now = s₂.now)
    (hpending : s₁.pending = s₂.pending) : trigger.dueTime s₁ = trigger.dueTime s₂ := by
  funext page
  cases trigger with
  | threshold δ => simp only [Trigger.dueTime, thresholdTime, hnow, pendingCost_congr hpending]
  | deadline => simp only [Trigger.dueTime, deadlineTime, hnow, hpending]

private theorem nextPayment?_congr {s₁ s₂ : State Page} (hnow : s₁.now = s₂.now)
    (hpending : s₁.pending = s₂.pending) : nextPayment? trigger s₁ = nextPayment? trigger s₂ := by
  simp only [nextPayment?, pendingPages, hpending, dueTime_congr hnow hpending]

private theorem nextAction?_congr {s₁ s₂ : State Page}
    (hhead : s₁.unseen.head? = s₂.unseen.head?)
    (hpayment : nextPayment? trigger s₁ = nextPayment? trigger s₂) : nextAction? trigger s₁ = nextAction? trigger s₂ := by
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
          cases hpair : nextPayment? trigger s₂ with
          | none => simp [nextAction?, h₁, h₂, hpayment, hpair]
          | some pair =>
              obtain ⟨time, page⟩ := pair
              simp [nextAction?, h₁, h₂, hpayment, hpair]

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

private theorem mirror_earlyPayments (input : Instance Page) (t : Time) :
    ∀ (fuel : ℕ) (s₁ s₂ : State Page), TimeInvariant s₁ → TimeInvariant s₂ →
      Mirror t s₁ s₂ →
      earlyPayments t (run trigger input fuel s₁) = earlyPayments t (run trigger input fuel s₂) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s₁ s₂ _ _ mirror
      simp [run, earlyPayments, mirror.payments_eq]
  | succ fuel ih =>
      intro s₁ s₂ htime₁ htime₂ mirror
      obtain ⟨shared, rest₁, rest₂, h₁, h₂, hrest₁, hrest₂⟩ := mirror.unseen_split
      have hpayment : nextPayment? trigger s₁ = nextPayment? trigger s₂ :=
        nextPayment?_congr mirror.now_eq mirror.pending_eq
      have advance : ∀ action, nextAction? trigger s₁ = some action → nextAction? trigger s₂ = some action →
          earlyPayments t (run trigger input (fuel + 1) s₁) =
            earlyPayments t (run trigger input (fuel + 1) s₂) := by
        intro action ha₁ ha₂
        simp only [run, ha₁, ha₂]
        exact ih _ _ (step_timeInvariant input s₁ action htime₁ ha₁)
          (step_timeInvariant input s₂ action htime₂ ha₂) (mirror.step input action)
      cases shared with
      | cons head tail =>
          have hhead : s₁.unseen.head? = s₂.unseen.head? := by simp [h₁, h₂]
          have haction : nextAction? trigger s₁ = nextAction? trigger s₂ := nextAction?_congr hhead hpayment
          cases ha₁ : nextAction? trigger s₁ with
          | none =>
              have ha₂ : nextAction? trigger s₂ = none := by rw [← haction, ha₁]
              simp [run, ha₁, ha₂, earlyPayments, mirror.payments_eq]
          | some action =>
              exact advance action ha₁ (by rw [← haction, ha₁])
      | nil =>
          simp only [List.nil_append] at h₁ h₂
          have hunseen₁ : ∀ occurrence ∈ s₁.unseen, t < occurrence.request.arrival := by
            rw [h₁]; exact hrest₁
          have hunseen₂ : ∀ occurrence ∈ s₂.unseen, t < occurrence.request.arrival := by
            rw [h₂]; exact hrest₂
          by_cases hdue : ∃ time page, nextPayment? trigger s₁ = some (time, page) ∧ time ≤ t
          · obtain ⟨time, page, hselected, hle⟩ := hdue
            refine advance (.payment time page)
              (nextAction_payment_of_late_unseen hselected hunseen₁ hle)
              (nextAction_payment_of_late_unseen (hpayment ▸ hselected) hunseen₂ hle)
          · push_neg at hdue
            have hlate₁ : ∀ time page, nextPayment? trigger s₁ = some (time, page) → t < time :=
              hdue
            have hlate₂ : ∀ time page, nextPayment? trigger s₂ = some (time, page) → t < time := by
              intro time page hselected
              exact hlate₁ time page (by rw [hpayment]; exact hselected)
            rw [no_early_payments input t _ s₁ htime₁ hunseen₁ hlate₁,
              no_early_payments input t _ s₂ htime₂ hunseen₂ hlate₂]
            simp [earlyPayments, mirror.payments_eq]

/-! ## The main statement -/

/-- FIFO's behaviour before time `t` is what it would have been on the request
sequence truncated at `t`. -/
theorem schedule_upTo_eq (input : Instance Page) (t : Time) :
    (schedule trigger input).upTo t = (schedule trigger (input.upTo t)).upTo t := by
  obtain ⟨count, hfilter, hdrop⟩ :=
    filter_eq_take_of_chronological (requests := input.requests) input.chronological t
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
  have hraise : run trigger (input.upTo t) (2 * (input.upTo t).requests.length)
        (initialState (input.upTo t)) =
      run trigger input (2 * input.requests.length) (initialState (input.upTo t)) := by
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
  have hpayments := mirror_earlyPayments (trigger := trigger) input t (2 * input.requests.length)
    (initialState input) (initialState (input.upTo t))
    (initial_timeInvariant input) (initial_timeInvariant (input.upTo t))
    hmirror
  unfold earlyPayments at hpayments
  unfold Schedule.upTo
  apply congrArg (Schedule.mk input.initialCache.toFinset)
  rw [schedule_events, schedule_events, filter_map_fetchEvent, filter_map_fetchEvent,
    hraise]
  exact congrArg (List.map Payment.fetchEvent) hpayments

/-- **FIFO is an online algorithm**, for every choice of thresholds.  The
truncated instance has the same cache size, hence the same threshold. -/
theorem algorithm_online (threshold : ℕ → Cost) :
    Algorithm.Online (FIFO.algorithm threshold (Page := Page)) :=
  Algorithm.online_of_upTo_eq fun input t =>
    schedule_upTo_eq (trigger := .threshold (threshold input.cacheSize)) input t

/-- **Deadline-triggered FIFO is an online algorithm.** -/
theorem deadlineAlgorithm_online :
    (FIFO.deadlineAlgorithm (Page := Page)).Online :=
  Algorithm.online_of_upTo_eq fun input t => schedule_upTo_eq (trigger := .deadline) input t

end
end PagingWithDelay.FIFO
