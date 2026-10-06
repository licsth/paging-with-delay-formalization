import EventLoop

/-!
# Basic facts about the event loop

What `nextPayment?` and `nextAction?` select, termination of `run` within its fuel, and the
reachable states, along which all later invariants are proved by induction.
-/

namespace PagingWithDelay.FIFO
variable {Page : Type*} [DecidableEq Page] {trigger : Trigger}
noncomputable section

/-! ## Selecting a payment -/

omit [DecidableEq Page] in
private theorem foldPayment_some (xs : List (Time × Page)) (best : Time × Page) :
    xs.foldl
      (fun best candidate =>
        some (match best with
          | none => candidate
          | some current => earlierPayment current candidate)) (some best) =
      some (xs.foldl earlierPayment best) := by
  induction xs generalizing best with
  | nil => rfl
  | cons x xs ih => exact ih _

/-- `nextPayment?` is a plain fold of `earlierPayment` over the candidates of the pending pages. -/
theorem nextPayment?_eq (trigger : Trigger) (state : State Page) :
    nextPayment? trigger state =
      match (pendingPages state).map fun page => (trigger.dueTime state page, page) with
      | [] => none
      | first :: rest => some (rest.foldl earlierPayment first) := by
  unfold nextPayment?
  generalize (pendingPages state).map _ = candidates
  cases candidates with
  | nil => rfl
  | cons first rest => exact foldPayment_some rest first

omit [DecidableEq Page] in
/-- A fold of `earlierPayment` returns its start or one of the candidates, and its time is
no later than any of them. -/
theorem foldl_earlierPayment (xs : List (Time × Page)) (best : Time × Page) :
    (xs.foldl earlierPayment best = best ∨ xs.foldl earlierPayment best ∈ xs) ∧
      (xs.foldl earlierPayment best).1 ≤ best.1 ∧
      ∀ candidate ∈ xs, (xs.foldl earlierPayment best).1 ≤ candidate.1 := by
  induction xs generalizing best with
  | nil => simp
  | cons x xs ih =>
      obtain ⟨hmem, hbest, hall⟩ := ih (earlierPayment best x)
      have hle : (earlierPayment best x).1 ≤ best.1 ∧ (earlierPayment best x).1 ≤ x.1 := by
        unfold earlierPayment; split <;> constructor <;> order
      have hcases : earlierPayment best x = best ∨ earlierPayment best x = x := by
        unfold earlierPayment; split <;> simp
      simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
      refine ⟨?_, hbest.trans hle.1, hbest.trans hle.2, hall⟩
      rcases hmem with h | h
      · rw [h]; rcases hcases with h | h <;> simp [h]
      · exact .inr (.inr h)

omit [DecidableEq Page] in
theorem mem_eraseDups {α : Type*} [BEq α] [LawfulBEq α] {a : α} :
    ∀ {l : List α}, a ∈ l.eraseDups ↔ a ∈ l
  | [] => by simp
  | b :: l => by
      have : (l.filter fun c => !c == b).length < l.length + 1 :=
        Nat.lt_succ_of_le (List.length_filter_le _ _)
      rw [List.eraseDups_cons, List.mem_cons, List.mem_cons, mem_eraseDups, List.mem_filter]
      by_cases h : a = b <;> simp [h]
termination_by l => l.length

theorem mem_pendingPages {state : State Page} {page : Page} :
    page ∈ pendingPages state ↔ ∃ occurrence ∈ state.pending, occurrence.request.page = page := by
  simp [pendingPages, mem_eraseDups]

/-- `nextPayment?` selects a pending page with the earliest due time. -/
theorem nextPayment_spec {state : State Page} {time : Time} {page : Page}
    (h : nextPayment? trigger state = some (time, page)) :
    page ∈ pendingPages state ∧ trigger.dueTime state page = time ∧
      ∀ other ∈ pendingPages state, time ≤ trigger.dueTime state other := by
  rw [nextPayment?_eq] at h
  cases hpages : pendingPages state with
  | nil => simp [hpages] at h
  | cons first rest =>
      simp only [hpages, List.map_cons, Option.some.injEq] at h
      obtain ⟨hmem, hfirst, hall⟩ := foldl_earlierPayment
        (rest.map fun page => (trigger.dueTime state page, page)) (trigger.dueTime state first, first)
      rw [h] at hmem hfirst hall
      simp only [List.forall_mem_map] at hall
      refine ⟨?_, ?_, List.forall_mem_cons.2 ⟨hfirst, hall⟩⟩ <;>
        rcases hmem with hmem | hmem <;> simp_all [Prod.ext_iff]

theorem nextPayment_mem_pendingPages {state : State Page} {time : Time} {page : Page}
    (h : nextPayment? trigger state = some (time, page)) : page ∈ pendingPages state :=
  (nextPayment_spec h).1

/-- A selected payment carries exactly the due time of its page. -/
theorem nextPayment_time_eq {state : State Page} {time : Time} {page : Page}
    (h : nextPayment? trigger state = some (time, page)) : trigger.dueTime state page = time :=
  (nextPayment_spec h).2.1

/-- The selected payment time is no later than the due time of any pending page. -/
theorem nextPayment_time_le_dueTime {state : State Page} {time : Time} {selected page : Page}
    (h : nextPayment? trigger state = some (time, selected)) (hpage : page ∈ pendingPages state) :
    time ≤ trigger.dueTime state page :=
  (nextPayment_spec h).2.2 page hpage

/-- A selected page has a pending request. -/
theorem nextPayment_pending {state : State Page} {time : Time} {page : Page}
    (h : nextPayment? trigger state = some (time, page)) :
    ∃ occurrence ∈ state.pending, occurrence.request.page = page :=
  mem_pendingPages.1 (nextPayment_mem_pendingPages h)

/-- While some request is pending, a payment is selected. -/
theorem nextPayment_exists_of_pending {state : State Page} {page : Page}
    (hpage : ∃ occurrence ∈ state.pending, occurrence.request.page = page) :
    ∃ time selected, nextPayment? trigger state = some (time, selected) := by
  have hmem := mem_pendingPages.2 hpage
  rw [nextPayment?_eq]
  cases hpages : pendingPages state with
  | nil => simp [hpages] at hmem
  | cons first rest => exact ⟨_, _, rfl⟩

/-! ## Selecting an action -/

/-- An arrival is the head of `unseen`, no later than any selected payment. -/
theorem nextAction_arrival {state : State Page} {occurrence : Occurrence Page}
    (h : nextAction? trigger state = some (.arrival occurrence)) :
    state.unseen = occurrence :: state.unseen.tail ∧
      ∀ time page, nextPayment? trigger state = some (time, page) →
        occurrence.request.arrival ≤ time := by
  unfold nextAction? at h
  split at h <;> (try split at h) <;> simp_all

/-- A payment is the selected one, strictly before the next arrival. -/
theorem nextAction_payment {state : State Page} {time : Time} {page : Page}
    (h : nextAction? trigger state = some (.payment time page)) :
    nextPayment? trigger state = some (time, page) ∧
      ∀ occurrence ∈ state.unseen.head?, time < occurrence.request.arrival := by
  unfold nextAction? at h
  split at h <;> (try split at h) <;> simp_all

theorem arrival_mem_unseen {state : State Page} {occurrence : Occurrence Page}
    (h : nextAction? trigger state = some (.arrival occurrence)) : occurrence ∈ state.unseen := by
  rw [(nextAction_arrival h).1]; simp

theorem nextAction_payment_selected {state : State Page} {time : Time} {page : Page}
    (h : nextAction? trigger state = some (.payment time page)) :
    nextPayment? trigger state = some (time, page) :=
  (nextAction_payment h).1

/-! ## Termination -/

def potential (state : State Page) : ℕ :=
  2 * state.unseen.length + state.pending.length

omit [DecidableEq Page] in
@[simp] theorem enumerateFrom_length (start : ℕ) (requests : List (Request Page)) :
    (enumerateFrom start requests).length = requests.length := by
  induction requests generalizing start <;> simp_all [enumerateFrom]

theorem potential_initialState (input : Instance Page) :
    potential (initialState input) = 2 * input.requests.length := by
  simp [potential, initialState, enumerate]

theorem nextAction_step_potential_lt (input : Instance Page) (state : State Page)
    (action : Action Page) (haction : nextAction? trigger state = some action) :
    potential (step input state action) < potential state := by
  cases action with
  | arrival occurrence =>
      have hu := (nextAction_arrival haction).1
      simp only [potential, step]
      rw [hu]
      split <;> simp
      omega
  | payment time page =>
      obtain ⟨occurrence, hmem, hpage⟩ := nextPayment_pending (nextAction_payment_selected haction)
      have hlt : (state.pending.filter fun o => o.request.page ≠ page).length <
          state.pending.length :=
        List.length_filter_lt_length_iff_exists.2 ⟨occurrence, hmem, by simpa using hpage⟩
      simp only [potential, step]
      omega

theorem run_finished_of_potential_le (input : Instance Page) (state : State Page) :
    ∀ fuel, potential state ≤ fuel →
      nextAction? trigger (run trigger input fuel state) = none := by
  intro fuel
  induction fuel generalizing state with
  | zero =>
      intro hpotential
      have hunseen : state.unseen = [] := by simp_all [potential]
      have hpending : state.pending = [] := by simp_all [potential]
      cases hp : nextPayment? trigger state with
      | none => simp [run, nextAction?, hunseen, hp]
      | some payment => simpa [hpending] using nextPayment_pending (trigger := trigger) hp
  | succ fuel ih =>
      intro hpotential
      rw [run]
      cases ha : nextAction? trigger state with
      | none => simp [ha]
      | some action =>
          have := nextAction_step_potential_lt input state action ha
          exact ih _ (by omega)

theorem run_initial_finished (input : Instance Page) :
    nextAction? trigger (run trigger input (2 * input.requests.length) (initialState input)) = none :=
  run_finished_of_potential_le input _ _ (potential_initialState input).le

/-! ## Reachable states -/

/-- The states the event loop reaches from its initial state. -/
inductive Reachable (trigger : Trigger) (input : Instance Page) : State Page → Prop
  | initial : Reachable trigger input (initialState input)
  | step {state : State Page} {action : Action Page} : Reachable trigger input state →
      nextAction? trigger state = some action → Reachable trigger input (step input state action)

theorem Reachable.run {input : Instance Page} {state : State Page}
    (h : Reachable trigger input state) (fuel : ℕ) :
    Reachable trigger input (FIFO.run trigger input fuel state) := by
  induction fuel generalizing state with
  | zero => exact h
  | succ fuel ih =>
      rw [FIFO.run]
      cases ha : nextAction? trigger state with
      | none => exact h
      | some action => exact ih (h.step ha)

theorem reachable_final (input : Instance Page) :
    Reachable trigger input (run trigger input (2 * input.requests.length) (initialState input)) :=
  Reachable.initial.run _

end
end PagingWithDelay.FIFO
