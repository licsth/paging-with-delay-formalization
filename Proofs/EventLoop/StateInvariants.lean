import Proofs.EventLoop.RunInvariants

namespace PagingWithDelay.FIFO
variable {Page : Type*} [DecidableEq Page] {trigger : Trigger}
noncomputable section

/-- The purely combinatorial part of the FIFO state invariant. -/
structure CacheInvariant (input : Instance Page) (state : State Page) : Prop where
  queue_nodup : state.queue.Nodup
  queue_capacity : state.queue.length ≤ input.cacheSize
  pending_miss : ∀ occurrence ∈ state.pending, occurrence.request.page ∉ state.queue

theorem initial_cacheInvariant (input : Instance Page) :
    CacheInvariant input (initialState input) :=
  ⟨input.initialCache_nodup, input.initialCache_full.le, by simp [initialState]⟩

omit [DecidableEq Page] in private theorem insertPage_nodup
    (capacity : ℕ) (queue : List Page) (page : Page)
    (hnodup : queue.Nodup) (hpage : page ∉ queue) :
    (insertPage capacity queue page).Nodup := by
  unfold insertPage
  split
  · exact List.Nodup.append hnodup (by simp) (by simpa using hpage)
  · exact List.Nodup.append hnodup.tail (by simp) (by simpa using mt List.mem_of_mem_tail hpage)

omit [DecidableEq Page] in private theorem insertPage_length_le
    (capacity : ℕ) (queue : List Page) (page : Page)
    (hcapacity : queue.length ≤ capacity) (hpositive : 0 < capacity) :
    (insertPage capacity queue page).length ≤ capacity := by
  unfold insertPage
  split <;> simp_all
  cases queue <;> simp_all

omit [DecidableEq Page] in private theorem mem_insertPage
    (capacity : ℕ) (queue : List Page) (page candidate : Page)
    (hmem : candidate ∈ insertPage capacity queue page) :
    candidate ∈ queue ∨ candidate = page := by
  unfold insertPage at hmem
  split at hmem <;> simp only [List.mem_append, List.mem_singleton] at hmem
  · exact hmem
  · exact hmem.imp_left List.mem_of_mem_tail

theorem step_cacheInvariant (input : Instance Page)
    (state : State Page) (action : Action Page)
    (hinv : CacheInvariant input state)
    (haction : nextAction? trigger state = some action) :
    CacheInvariant input (step input state action) := by
  cases action with
  | arrival occurrence =>
    constructor
    · exact hinv.queue_nodup
    · exact hinv.queue_capacity
    · intro pending hpending
      simp only [step] at hpending ⊢
      split at hpending
      · exact hinv.pending_miss pending hpending
      · simp only [List.mem_append, List.mem_singleton] at hpending
        rcases hpending with hpending | rfl
        · exact hinv.pending_miss pending hpending
        · assumption
  | payment time page =>
    obtain ⟨served, hserved, hserved_page⟩ :=
      nextPayment_pending (nextAction_payment_selected haction)
    have hpage : page ∉ state.queue := by
      rw [← hserved_page]
      exact hinv.pending_miss served hserved
    constructor
    · exact insertPage_nodup _ _ _ hinv.queue_nodup hpage
    · exact insertPage_length_le _ _ _ hinv.queue_capacity input.positiveCapacity
    · intro pending hpending hcache
      simp only [step, List.mem_filter] at hpending
      obtain ⟨hpending_old, hpending_ne⟩ := hpending
      obtain hold | hnew := mem_insertPage _ _ _ _ hcache
      · exact hinv.pending_miss pending hpending_old hold
      · exact (of_decide_eq_true hpending_ne) hnew

theorem Reachable.cacheInvariant {input : Instance Page} {state : State Page}
    (h : Reachable trigger input state) : CacheInvariant input state := by
  induction h with
  | initial => exact initial_cacheInvariant input
  | step _ ha ih => exact step_cacheInvariant input _ _ ih ha

end
end PagingWithDelay.FIFO
