import EventLoop

namespace PagingWithDelay.FIFO
variable {Page : Type*} [DecidableEq Page] {trigger : Trigger}
noncomputable section

def potential (state : State Page) : ℕ :=
  2 * state.unseen.length + state.pending.length

omit [DecidableEq Page] in theorem foldPayment_mem
    (xs : List (Time × Page)) (best : Option (Time × Page))
    {result : Time × Page}
    (h : xs.foldl
      (fun best candidate =>
        some (match best with
          | none => candidate
          | some current => earlierPayment current candidate)) best = some result) :
    result ∈ xs ∨ best = some result := by
  induction xs generalizing best result with
  | nil => exact Or.inr h
  | cons x xs ih =>
      simp only [List.foldl_cons] at h
      obtain hmem | heq := ih _ h
      · exact Or.inl (List.mem_cons_of_mem x hmem)
      · rcases best with _ | current
        · simp at heq
          subst result
          exact Or.inl (by simp)
        · simp only [earlierPayment] at heq
          split at heq
          · have her : x = result := Option.some.inj heq
            exact Or.inl (by simp [her])
          · exact Or.inr heq

theorem nextPayment_mem_pendingPages {state : State Page} {time : Time} {page : Page}
    (h : nextPayment? trigger state = some (time, page)) : page ∈ pendingPages state := by
  unfold nextPayment? at h
  obtain hm | impossible := foldPayment_mem _ none h
  · simp only [List.mem_map] at hm
    obtain ⟨p, hp, hpair⟩ := hm
    have hpage : p = page := congrArg Prod.snd hpair
    simpa [hpage] using hp
  · simp at impossible

theorem pending_of_mem_pendingPages {state : State Page} {page : Page}
    (h : page ∈ pendingPages state) :
    ∃ occurrence ∈ state.pending, occurrence.request.page = page := by
  unfold pendingPages at h
  have hm : page ∈ state.pending.map (fun occurrence => occurrence.request.page) := by
    let xs := state.pending.map (fun occurrence => occurrence.request.page)
    have loop_mem : ∀ (as bs : List Page),
        page ∈ List.eraseDupsBy.loop (fun x y : Page => x == y) as bs →
          page ∈ as ∨ page ∈ bs := by
      intro as
      induction as with
      | nil =>
        intro bs hmem
        exact Or.inr (by simpa [List.eraseDupsBy.loop] using hmem)
      | cons head tail ih =>
        intro bs hmem
        simp only [List.eraseDupsBy.loop] at hmem
        split at hmem
        · obtain htail | hbs := ih bs hmem
          · exact Or.inl (List.mem_cons_of_mem head htail)
          · exact Or.inr hbs
        · obtain htail | hbs := ih (head :: bs) hmem
          · exact Or.inl (List.mem_cons_of_mem head htail)
          · simp only [List.mem_cons] at hbs
            rcases hbs with heq | hbs
            · exact Or.inl (by simp [heq])
            · exact Or.inr hbs
    unfold List.eraseDups List.eraseDupsBy at h
    obtain hx | impossible := loop_mem xs [] h
    · exact hx
    · simp at impossible
  simpa only [List.mem_map] using hm

private theorem length_filter_lt_of_exists {state : State Page} {page : Page}
    (h : ∃ occurrence ∈ state.pending, occurrence.request.page = page) :
    (state.pending.filter fun occurrence => occurrence.request.page ≠ page).length <
      state.pending.length := by
  have aux : ∀ xs : List (Occurrence Page),
      (∃ occurrence ∈ xs, occurrence.request.page = page) →
      (xs.filter fun occurrence => occurrence.request.page ≠ page).length < xs.length := by
    intro xs hexists
    induction xs with
    | nil => simp at hexists
    | cons head tail ih =>
      by_cases hp : head.request.page = page
      · simp [hp]
        exact List.length_filter_le _ _
      · have htail : ∃ occurrence ∈ tail,
            occurrence.request.page = page := by
          obtain ⟨occurrence, hmem, heq⟩ := hexists
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact (hp heq).elim
          · exact ⟨occurrence, hmem, heq⟩
        simpa [hp] using ih htail
  exact aux state.pending h

theorem nextAction_step_potential_lt (input : Instance Page) (state : State Page)
    (action : Action Page) (haction : nextAction? trigger state = some action) :
    potential (step input state action) < potential state := by
  unfold nextAction? at haction
  cases hu : state.unseen with
  | nil =>
    cases hp : nextPayment? trigger state with
    | none => simp [hu, hp] at haction
    | some payment =>
      simp only [hu, hp] at haction
      injection haction with haction
      subst action
      rcases payment with ⟨time, page⟩
      have hpage := nextPayment_mem_pendingPages hp
      have hlt := length_filter_lt_of_exists (pending_of_mem_pendingPages hpage)
      simp only [potential, step, hu, List.length_nil]
      omega
  | cons occurrence unseen =>
    cases hp : nextPayment? trigger state with
    | none =>
      simp only [hu, hp] at haction
      injection haction with haction
      subst action
      simp only [potential, step, hu, List.tail_cons, List.length_cons]
      split <;> simp_all
      omega
    | some payment =>
      rcases payment with ⟨time, page⟩
      simp only [hu, hp] at haction
      split at haction
      · injection haction with haction
        subst action
        simp only [potential, step, hu, List.tail_cons, List.length_cons]
        split <;> simp_all
        omega
      · injection haction with haction
        subst action
        have hpage := nextPayment_mem_pendingPages hp
        have hlt := length_filter_lt_of_exists (pending_of_mem_pendingPages hpage)
        simp only [potential, step, hu, List.length_cons]
        omega

theorem run_finished_of_potential_le (input : Instance Page) (state : State Page) :
    ∀ fuel, potential state ≤ fuel →
      nextAction? trigger (run trigger input fuel state) = none := by
  intro fuel
  induction fuel generalizing state with
  | zero =>
      intro hpotential
      have hz : potential state = 0 := Nat.eq_zero_of_le_zero hpotential
      cases hu : state.unseen with
      | nil =>
        cases hp : nextPayment? trigger state with
        | none => simp [run, nextAction?, hu, hp]
        | some payment =>
          have hpage := nextPayment_mem_pendingPages hp
          obtain ⟨request, hmem, _⟩ := pending_of_mem_pendingPages hpage
          have hpending : state.pending ≠ [] := by
            intro hempty
            simp [hempty] at hmem
          exfalso
          apply hpending
          cases hs : state.pending with
          | nil => rfl
          | cons head tail =>
            simp [potential, hu, hs] at hz
      | cons occurrence unseen => simp [potential, hu] at hz
  | succ fuel ih =>
      intro hpotential
      rw [run]
      cases ha : nextAction? trigger state with
      | none => simp [ha]
      | some action =>
        simp only
        apply ih
        have hlt := nextAction_step_potential_lt input state action ha
        omega

theorem run_initial_finished (input : Instance Page) :
    nextAction? trigger (run trigger input (2 * input.requests.length) (initialState input)) = none := by
  apply run_finished_of_potential_le
  suffices ∀ n, (enumerateFrom n input.requests).length = input.requests.length by
    simp [potential, initialState, enumerate, this]
  intro n
  induction input.requests generalizing n with
  | nil => rfl
  | cons head tail ih => simp [enumerateFrom, ih]

end
end PagingWithDelay.FIFO
