import Proofs.Basic.Nonclairvoyant
import Proofs.EventLoop.Observation
import Algorithm

/-!
# FIFO is nonclairvoyant, for every trigger

This file proves `Algorithm.Nonclairvoyant` for threshold FIFO, for every
threshold: what the algorithm does up to a time `t` depends only on what the
input has revealed by `t` — the requests that have arrived, and the delay each
of them has accrued so far — and not on the delay curves that produce that
delay.  It proves `DeadlineAlgorithm.Nonclairvoyant` for deadline-triggered
FIFO: what it does up to `t` depends only on the requests that have arrived and
those of their deadlines that have been reached.

Both are instances of one simulation, parameterized by the relation `R t` of
two requests that have revealed the same thing by `t` (`Reveals`).

## Strategy

The proof is the one for onlineness (`Proofs/FIFO/Online.lean`) with
the simulation relaxed, and it reuses that proof's machinery from
`Proofs/EventLoop/RunComparison.lean`: a common fuel by
`run_eq_of_le`, a common instance by `run_congr`, and `no_early_payments` for
the tail of a run.  Two differences remain, and they are what
`Proofs/EventLoop/Observation.lean` is for.

* **The two runs never reach a common state.**  Their pending requests carry
  different delay curves, so `Mirror` below relates states only up to `t`:
  equal clocks, queues and public payment logs, but pending and unseen
  occurrences merely related by `R t`.  The payment logs are compared through
  `Payment.fetchEvent`, which is all the public schedule shows; the internal
  record of *which* occurrences a payment served cannot agree, and does not
  have to.
* **The two runs need not select the same payment.**  `Reveals.payment`
  gives only that the selected payments coincide *or* both fall strictly after
  `t`.  That suffices: an action taken after `t` moves the clock past `t`, and
  `late_payments` then shows the rest of the run adds nothing the public
  schedule shows at or before `t`.

The clock staying at or before `t` while the simulation runs is therefore part
of `Mirror`, and every action the simulation takes is shown to be stamped no
later than `t`.
-/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page] {trigger : Trigger}
  {R : Time → Request Page → Request Page → Prop}

noncomputable section

/-- What the simulation needs of `R t`, the relation of two requests that
have revealed the same thing by `t`: it preserves page and arrival, and states
whose pending requests are related select agreeing payments. -/
structure Reveals (trigger : Trigger) (R : Time → Request Page → Request Page → Prop) :
    Prop where
  page : ∀ {t first second}, R t first second → first.page = second.page
  arrival : ∀ {t first second}, R t first second → first.arrival = second.arrival
  payment : ∀ {t : Time} {s₁ s₂ : State Page}, s₁.now = s₂.now →
    List.Forall₂ (OccurrenceRel (R t)) s₁.pending s₂.pending →
    BelowThreshold trigger.level s₁ → BelowThreshold trigger.level s₂ →
    PaymentAgree t (nextPayment? trigger s₁) (nextPayment? trigger s₂)

/-- The time an action is stamped with, which is by definition the clock of the
state the action steps to: `(step input state action).now = actionTime action`
holds by `rfl`, and `Mirror.step` below uses it as such. -/
private def actionTime : Action Page → Time
  | .arrival occurrence => occurrence.request.arrival
  | .payment time _ => time

/-- Two actions that do the same thing as far as anything revealed by `t` is
concerned. -/
private inductive ActionAgree (R : Time → Request Page → Request Page → Prop) (t : Time) : Action Page → Action Page → Prop
  | arrival {first second : Occurrence Page} (agree : OccurrenceRel (R t) first second) :
      ActionAgree R t (.arrival first) (.arrival second)
  | payment (time : Time) (page : Page) :
      ActionAgree R t (.payment time page) (.payment time page)

/-! ## The simulation -/

/-- Two event-loop states that have been told the same story up to `t`: equal
clocks, still at or before `t`, equal queues, equal public payment logs, and
pending and unseen occurrences that agree as far as `t` reveals them.  Beyond
the shared prefix of the unseen lists nothing is asked: those requests arrive
after `t`. -/
private structure Mirror (R : Time → Request Page → Request Page → Prop) (t : Time) (s₁ s₂ : State Page) : Prop where
  now_eq : s₁.now = s₂.now
  now_le : s₁.now ≤ t
  queue_eq : s₁.queue = s₂.queue
  pending_agree : List.Forall₂ (OccurrenceRel (R t)) s₁.pending s₂.pending
  payments_agree : s₁.payments.map Payment.fetchEvent = s₂.payments.map Payment.fetchEvent
  unseen_split : ∃ shared₁ shared₂ rest₁ rest₂,
    s₁.unseen = shared₁ ++ rest₁ ∧ s₂.unseen = shared₂ ++ rest₂ ∧
      List.Forall₂ (OccurrenceRel (R t)) shared₁ shared₂ ∧
      (∀ occurrence ∈ shared₁, occurrence.request.arrival ≤ t) ∧
      (∀ occurrence ∈ rest₁, t < occurrence.request.arrival) ∧
      (∀ occurrence ∈ rest₂, t < occurrence.request.arrival)

private theorem Mirror.step (obs : Reveals trigger R) (input : Instance Page) {t : Time} {s₁ s₂ : State Page}
    (mirror : Mirror R t s₁ s₂) {action₁ action₂ : Action Page}
    (agree : ActionAgree R t action₁ action₂) (hearly : actionTime action₁ ≤ t) :
    Mirror R t (FIFO.step input s₁ action₁) (FIFO.step input s₂ action₂) := by
  obtain ⟨shared₁, shared₂, rest₁, rest₂, h₁, h₂, hshared, hshared_early, hrest₁, hrest₂⟩ :=
    mirror.unseen_split
  cases agree with
  | @arrival first second hoccurrence =>
      have hpage : first.request.page = second.request.page := obs.page hoccurrence
      have harrival : first.request.arrival = second.request.arrival :=
        obs.arrival hoccurrence
      refine ⟨harrival, hearly, mirror.queue_eq, ?_, mirror.payments_agree, ?_⟩
      · show List.Forall₂ (OccurrenceRel (R t))
          (if first.request.page ∈ s₁.queue then s₁.pending else s₁.pending ++ [first])
          (if second.request.page ∈ s₂.queue then s₂.pending else s₂.pending ++ [second])
        rw [← hpage, ← mirror.queue_eq]
        by_cases hmem : first.request.page ∈ s₁.queue
        · rw [if_pos hmem, if_pos hmem]
          exact mirror.pending_agree
        · rw [if_neg hmem, if_neg hmem]
          exact List.rel_append mirror.pending_agree
            (List.Forall₂.cons hoccurrence List.Forall₂.nil)
      · cases hshared with
        | nil =>
            exact ⟨[], [], rest₁.tail, rest₂.tail, by simp [FIFO.step, h₁],
              by simp [FIFO.step, h₂], List.Forall₂.nil, by simp,
              fun occurrence hoccurrence => hrest₁ occurrence (List.mem_of_mem_tail hoccurrence),
              fun occurrence hoccurrence => hrest₂ occurrence (List.mem_of_mem_tail hoccurrence)⟩
        | @cons head₁ head₂ tail₁ tail₂ hheads htails =>
            exact ⟨tail₁, tail₂, rest₁, rest₂, by simp [FIFO.step, h₁], by simp [FIFO.step, h₂],
              htails, fun occurrence hoccurrence =>
                hshared_early occurrence (List.mem_cons_of_mem _ hoccurrence),
              hrest₁, hrest₂⟩
  | payment time page =>
      refine ⟨rfl, hearly, ?_, ?_, ?_,
        ⟨shared₁, shared₂, rest₁, rest₂, by simpa [FIFO.step] using h₁,
          by simpa [FIFO.step] using h₂, hshared, hshared_early, hrest₁, hrest₂⟩⟩
      · simp only [FIFO.step, mirror.queue_eq]
      · exact filter_agree obs.page mirror.pending_agree fun candidate => decide (candidate ≠ page)
      · simp only [FIFO.step, mirror.queue_eq, List.map_append, mirror.payments_agree]
        rfl

/-- The part of the payment log the public schedule shows at or before `t`. -/
private theorem earlyEvents_congr {t : Time} {s₁ s₂ : State Page}
    (hpayments : s₁.payments.map Payment.fetchEvent = s₂.payments.map Payment.fetchEvent) :
    (earlyPayments t s₁).map Payment.fetchEvent =
      (earlyPayments t s₂).map Payment.fetchEvent := by
  unfold earlyPayments
  rw [← filter_map_fetchEvent, ← filter_map_fetchEvent, hpayments]

/-- While an arrival is still to come at or before `t`, both states act, they
act alike, and they act no later than `t`. -/
private theorem nextAction_agree_of_early_head (obs : Reveals trigger R) {t : Time} {s₁ s₂ : State Page}
    {head₁ head₂ : Occurrence Page} {tail₁ tail₂ : List (Occurrence Page)}
    (hunseen₁ : s₁.unseen = head₁ :: tail₁) (hunseen₂ : s₂.unseen = head₂ :: tail₂)
    (hheads : OccurrenceRel (R t) head₁ head₂) (hearly : head₁.request.arrival ≤ t)
    (hpayment : PaymentAgree t (nextPayment? trigger s₁) (nextPayment? trigger s₂)) :
    ∃ action₁ action₂, nextAction? trigger s₁ = some action₁ ∧ nextAction? trigger s₂ = some action₂ ∧
      ActionAgree R t action₁ action₂ ∧ actionTime action₁ ≤ t := by
  have harrival : head₁.request.arrival = head₂.request.arrival :=
    obs.arrival hheads
  have arrivals : nextPayment? trigger s₁ = none → nextPayment? trigger s₂ = none := by
    intro hnone
    rcases hpayment with heq | ⟨_, _, hleft, _⟩
    · rw [← heq]; exact hnone
    · rw [hnone] at hleft; exact absurd hleft (by simp)
  cases hfirst : nextPayment? trigger s₁ with
  | none =>
      refine ⟨.arrival head₁, .arrival head₂, ?_, ?_, ActionAgree.arrival hheads, hearly⟩
      · simp [nextAction?, hunseen₁, hfirst]
      · simp [nextAction?, hunseen₂, arrivals hfirst]
  | some pair =>
      obtain ⟨time, page⟩ := pair
      by_cases hdue : time ≤ t
      · have hsecond : nextPayment? trigger s₂ = some (time, page) :=
          hpayment.eq_of_le hfirst hdue
        by_cases hbefore : head₁.request.arrival ≤ time
        · refine ⟨.arrival head₁, .arrival head₂, ?_, ?_, ActionAgree.arrival hheads, hearly⟩
          · simp [nextAction?, hunseen₁, hfirst, hbefore]
          · simp [nextAction?, hunseen₂, hsecond, ← harrival, hbefore]
        · refine ⟨.payment time page, .payment time page, ?_, ?_, ActionAgree.payment time page,
            le_of_lt (lt_of_lt_of_le (lt_of_not_ge hbefore) hearly)⟩
          · simp [nextAction?, hunseen₁, hfirst, hbefore]
          · simp [nextAction?, hunseen₂, hsecond, ← harrival, hbefore]
      · have hlate : t < time := lt_of_not_ge hdue
        obtain ⟨time₂, page₂, hsecond, hlate₂⟩ :
            ∃ time₂ page₂, nextPayment? trigger s₂ = some (time₂, page₂) ∧ t < time₂ := by
          rcases hpayment with heq | ⟨left, right, hleft, hright, _, hright_late⟩
          · exact ⟨time, page, by rw [← heq]; exact hfirst, hlate⟩
          · rw [hfirst] at hleft
            cases hleft
            exact ⟨right.1, right.2, hright, hright_late⟩
        have hbefore₁ : head₁.request.arrival ≤ time := hearly.trans hlate.le
        have hbefore₂ : head₂.request.arrival ≤ time₂ := by
          rw [← harrival]; exact hearly.trans hlate₂.le
        refine ⟨.arrival head₁, .arrival head₂, ?_, ?_, ActionAgree.arrival hheads, hearly⟩
        · simp [nextAction?, hunseen₁, hfirst, hbefore₁]
        · simp [nextAction?, hunseen₂, hsecond, hbefore₂]

private theorem mirror_earlyEvents (obs : Reveals trigger R) (input : Instance Page) (t : Time) :
    ∀ (fuel : ℕ) (s₁ s₂ : State Page), TimeInvariant s₁ → TimeInvariant s₂ →
      BelowThreshold trigger.level s₁ → BelowThreshold trigger.level s₂ → Mirror R t s₁ s₂ →
      (earlyPayments t (run trigger input fuel s₁)).map Payment.fetchEvent =
        (earlyPayments t (run trigger input fuel s₂)).map Payment.fetchEvent := by
  intro fuel
  induction fuel with
  | zero =>
      intro s₁ s₂ _ _ _ _ mirror
      simpa only [run] using earlyEvents_congr mirror.payments_agree
  | succ fuel ih =>
      intro s₁ s₂ htime₁ htime₂ hbelow₁ hbelow₂ mirror
      obtain ⟨shared₁, shared₂, rest₁, rest₂, h₁, h₂, hshared, hshared_early, hrest₁, hrest₂⟩ :=
        mirror.unseen_split
      have hpayment : PaymentAgree t (nextPayment? trigger s₁) (nextPayment? trigger s₂) :=
        obs.payment mirror.now_eq mirror.pending_agree hbelow₁ hbelow₂
      have advance : ∀ action₁ action₂, ActionAgree R t action₁ action₂ →
          actionTime action₁ ≤ t → nextAction? trigger s₁ = some action₁ →
          nextAction? trigger s₂ = some action₂ →
          (earlyPayments t (run trigger input (fuel + 1) s₁)).map Payment.fetchEvent =
            (earlyPayments t (run trigger input (fuel + 1) s₂)).map Payment.fetchEvent := by
        intro action₁ action₂ hagree hearly haction₁ haction₂
        simp only [run, haction₁, haction₂]
        exact ih _ _ (step_timeInvariant input s₁ action₁ htime₁ haction₁)
          (step_timeInvariant input s₂ action₂ htime₂ haction₂)
          (step_belowThreshold input s₁ action₁ hbelow₁ haction₁)
          (step_belowThreshold input s₂ action₂ hbelow₂ haction₂)
          (mirror.step obs input hagree hearly)
      cases hshared with
      | cons hheads htails =>
          rename_i head₁ head₂ tail₁ tail₂
          obtain ⟨action₁, action₂, haction₁, haction₂, hagree, hearly⟩ :=
            nextAction_agree_of_early_head obs (by rw [h₁]; rfl) (by rw [h₂]; rfl) hheads
              (hshared_early head₁ (by simp)) hpayment
          exact advance action₁ action₂ hagree hearly haction₁ haction₂
      | nil =>
          simp only [List.nil_append] at h₁ h₂
          have hunseen₁ : ∀ occurrence ∈ s₁.unseen, t < occurrence.request.arrival := by
            rw [h₁]; exact hrest₁
          have hunseen₂ : ∀ occurrence ∈ s₂.unseen, t < occurrence.request.arrival := by
            rw [h₂]; exact hrest₂
          by_cases hdue : ∃ time page, nextPayment? trigger s₁ = some (time, page) ∧ time ≤ t
          · obtain ⟨time, page, hselected, hle⟩ := hdue
            exact advance (.payment time page) (.payment time page)
              (ActionAgree.payment time page) hle
              (nextAction_payment_of_late_unseen hselected hunseen₁ hle)
              (nextAction_payment_of_late_unseen (hpayment.eq_of_le hselected hle) hunseen₂ hle)
          · push_neg at hdue
            have hlate₁ : ∀ time page, nextPayment? trigger s₁ = some (time, page) → t < time := hdue
            rw [no_early_payments input t _ s₁ htime₁ hunseen₁ hlate₁,
              no_early_payments input t _ s₂ htime₂ hunseen₂ (hpayment.late hlate₁)]
            exact earlyEvents_congr mirror.payments_agree

/-! ## Enumeration preserves what has been revealed -/

omit [DecidableEq Page] in
private theorem enumerateFrom_agree {t : Time} {first second : List (Request Page)}
    (agree : List.Forall₂ (R t) first second) :
    ∀ start₁ start₂ : ℕ,
      List.Forall₂ (OccurrenceRel (R t)) (enumerateFrom start₁ first)
        (enumerateFrom start₂ second) := by
  induction agree with
  | nil => intro _ _; simp [enumerateFrom]
  | cons hhead _ ih =>
      intro start₁ start₂
      exact List.Forall₂.cons hhead (ih (start₁ + 1) (start₂ + 1))

/-! ## The main statement -/

/-- FIFO's behaviour before `t` is determined by what the input has revealed
by `t`, in the sense of `R`. -/
theorem schedule_upTo_eq_of_reveals (obs : Reveals trigger R) (first second : Instance Page)
    (t : Time) (hcacheSize : first.cacheSize = second.cacheSize)
    (hinitialCache : first.initialCache = second.initialCache)
    (hrequests : List.Forall₂ (R t) (first.upTo t).requests (second.upTo t).requests) :
    (schedule trigger first).upTo t = (schedule trigger second).upTo t := by
  obtain ⟨count₁, hfilter₁, hdrop₁⟩ :=
    filter_eq_take_of_chronological (requests := first.requests) first.chronological t
  obtain ⟨count₂, hfilter₂, hdrop₂⟩ :=
    filter_eq_take_of_chronological (requests := second.requests) second.chronological t
  -- Give the two runs a common fuel, and read them over the same instance:
  -- only the cache capacity of that instance is ever consulted.
  set fuel := 2 * (first.requests.length + second.requests.length) with hfuel
  have hraise₁ : run trigger first (2 * first.requests.length) (initialState first) =
      run trigger first fuel (initialState first) :=
    (run_eq_of_le first (initialState first) (le_of_eq (potential_initialState first))
      (by omega)).symm
  have hraise₂ : run trigger second (2 * second.requests.length) (initialState second) =
      run trigger first fuel (initialState second) := by
    rw [← run_congr hcacheSize.symm fuel (initialState second)]
    exact (run_eq_of_le second (initialState second) (le_of_eq (potential_initialState second))
      (by omega)).symm
  -- The two initial states mirror each other.
  have hmirror : Mirror R t (initialState first) (initialState second) := by
    refine ⟨rfl, bot_le, hinitialCache, List.Forall₂.nil, rfl,
      ⟨enumerate (first.requests.take count₁), enumerate (second.requests.take count₂),
        (enumerate first.requests).drop count₁, (enumerate second.requests).drop count₂,
        ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · show enumerate first.requests = _
      simp only [enumerate, enumerateFrom_take]
      exact (List.take_append_drop count₁ (enumerateFrom 0 first.requests)).symm
    · show enumerate second.requests = _
      simp only [enumerate, enumerateFrom_take]
      exact (List.take_append_drop count₂ (enumerateFrom 0 second.requests)).symm
    · refine enumerateFrom_agree ?_ 0 0
      rw [show (first.upTo t).requests = first.requests.take count₁ from hfilter₁,
        show (second.upTo t).requests = second.requests.take count₂ from hfilter₂] at hrequests
      exact hrequests
    · intro occurrence hoccurrence
      have hmem : occurrence.request ∈ first.requests.take count₁ :=
        mem_enumerateFrom_request hoccurrence
      rw [← hfilter₁] at hmem
      simpa using (List.mem_filter.mp hmem).2
    · intro occurrence hoccurrence
      simp only [enumerate, enumerateFrom_drop_eq] at hoccurrence
      exact hdrop₁ occurrence.request (mem_enumerateFrom_request hoccurrence)
    · intro occurrence hoccurrence
      simp only [enumerate, enumerateFrom_drop_eq] at hoccurrence
      exact hdrop₂ occurrence.request (mem_enumerateFrom_request hoccurrence)
  have hevents := mirror_earlyEvents obs first t fuel
    (initialState first) (initialState second)
    (initial_timeInvariant first) (initial_timeInvariant second)
    (initial_belowThreshold first) (initial_belowThreshold second) hmirror
  unfold earlyPayments at hevents
  unfold Schedule.upTo
  rw [schedule_events, schedule_events, filter_map_fetchEvent, filter_map_fetchEvent,
    hraise₁, hraise₂]
  exact congrArg₂ Schedule.mk (by simp [schedule, hinitialCache]) hevents

/-! ## The two triggers -/

/-- The threshold trigger reads delay revealed so far. -/
theorem reveals_threshold (δ : Cost) :
    Reveals (Page := Page) (.threshold δ) fun t => Request.AgreeUpTo t where
  page agree := agree.page
  arrival agree := agree.arrival
  payment hnow agree hbelow₁ hbelow₂ := nextPayment?_agree_threshold hnow agree hbelow₁ hbelow₂

/-- The deadline trigger reads deadlines once they are reached. -/
theorem reveals_deadline :
    Reveals (Page := Page) .deadline fun t => Request.DeadlineAgreeUpTo t where
  page agree := agree.page
  arrival agree := agree.arrival
  payment hnow agree _ _ := nextPayment?_agree_deadline hnow agree

/-- **FIFO is a nonclairvoyant algorithm**, for every choice of thresholds.
Instances that agree up to a time have the same cache size, hence the same
threshold. -/
theorem algorithm_nonclairvoyant (threshold : ℕ → Cost) :
    Algorithm.Nonclairvoyant (FIFO.algorithm threshold (Page := Page)) where
  observationDetermined first second t agree := by
    show (schedule (.threshold (threshold first.cacheSize)) first).upTo t =
      (schedule (.threshold (threshold second.cacheSize)) second).upTo t
    rw [agree.cacheSize]
    exact schedule_upTo_eq_of_reveals (reveals_threshold _) first second t
      agree.cacheSize agree.initialCache agree.requests

/-- **Deadline-triggered FIFO is a nonclairvoyant deadline algorithm**: it
learns a deadline only when it is reached. -/
theorem deadlineAlgorithm_nonclairvoyant :
    (FIFO.deadlineAlgorithm (Page := Page)).Nonclairvoyant where
  observationDetermined first second t agree :=
    schedule_upTo_eq_of_reveals reveals_deadline first second t
      agree.cacheSize agree.initialCache agree.requests

end
end PagingWithDelay.FIFO
