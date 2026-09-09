import PagingWithDelay.EventLoop.FreshQueue
import PagingWithDelay.EventLoop.PaymentOrder

/-!
# History invariants of the FIFO run

Bookkeeping facts about the payment log that the event loop builds: batches
record occurrences of the page they fetch, arriving no later than the payment;
every retained occurrence comes from the input; occurrence identifiers are
never duplicated; and a pending request for a previously fetched page arrived
after that copy was evicted.

All of these are established by preserving an invariant through `step` and
lifting it along `run`.  None depends on the competitive analysis.
-/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page] {δ : Cost}

noncomputable section

namespace History

open FIFO

def PendingArrived (state : State Page) : Prop :=
  ∀ occurrence ∈ state.pending, occurrence.request.arrival ≤ state.now

def ValidBatches (state : State Page) : Prop :=
  ∀ payment ∈ state.payments, ∀ occurrence ∈ payment.served,
    occurrence.request.page = payment.page ∧
      occurrence.request.arrival ≤ payment.time

def Authentic (input : Instance Page) (state : State Page) : Prop :=
  (∀ occurrence ∈ state.unseen, occurrence ∈ enumerate input.requests) ∧
  (∀ occurrence ∈ state.pending, occurrence ∈ enumerate input.requests) ∧
  (∀ payment ∈ state.payments, ∀ occurrence ∈ payment.served,
    occurrence ∈ enumerate input.requests)

def trackedIds (state : State Page) : List ℕ :=
  ((state.payments.flatMap Payment.served) ++ state.pending ++ state.unseen).map Occurrence.id

def UniqueIds (state : State Page) : Prop := (trackedIds state).Nodup

def StrictUnseen (state : State Page) : Prop :=
  ∀ payment ∈ state.payments, ∀ occurrence ∈ state.unseen,
    payment.time < occurrence.request.arrival

/-- A pending request for a page that has previously been fetched arrived
strictly after that copy's FIFO eviction.  Indices are relative to the
payment prefix recorded in `state`. -/
def PendingSinceEviction (input : Instance Page) (state : State Page) : Prop :=
  ∀ occurrence ∈ state.pending, ∀ previous (hprevious : previous < state.payments.length),
    state.payments[previous].page = occurrence.request.page →
      previous + input.cacheSize < state.payments.length ∧
        (state.payments[previous + input.cacheSize]?).any
          (fun payment => payment.time < occurrence.request.arrival)

/-- The already recorded batches satisfy the lower endpoint of their payment
window. -/
def ValidBatchLowerBounds (input : Instance Page) (state : State Page) : Prop :=
  ∀ index (hindex : index < state.payments.length),
    ∀ occurrence ∈ state.payments[index].served,
      ∀ previous (hprevious : previous < index),
        state.payments[previous].page = state.payments[index].page →
          previous + input.cacheSize < index ∧
            (state.payments[previous + input.cacheSize]?).any
              (fun payment => payment.time < occurrence.request.arrival)

omit [DecidableEq Page] in private theorem enumerateFrom_ids
    (next : ℕ) (requests : List (Request Page)) :
    (enumerateFrom next requests).map Occurrence.id = List.range' next requests.length := by
  induction requests generalizing next with
  | nil => simp [enumerateFrom]
  | cons request rest ih => simp [enumerateFrom, ih, List.range'_succ]

theorem initial_uniqueIds (input : Instance Page) : UniqueIds (initialState input) := by
  simp [UniqueIds, trackedIds, initialState, enumerate, enumerateFrom_ids,
    List.nodup_range']

theorem initial_strictUnseen (input : Instance Page) : StrictUnseen (initialState input) := by
  simp [StrictUnseen, initialState]

omit [DecidableEq Page] in private theorem filter_partition_perm
    (p : Occurrence Page → Bool) :
    ∀ xs : List (Occurrence Page), List.Perm
      ((xs.filter p).map Occurrence.id ++
        (xs.filter fun x => !p x).map Occurrence.id)
      (xs.map Occurrence.id) := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hp : p x
      · simp [hp, ih]
      · simp [hp]
        exact List.perm_middle.trans (List.Perm.cons _ ih)

private theorem arrival_mem_unseen {state : State Page} {occurrence : Occurrence Page}
    (ha : nextAction? δ state = some (.arrival occurrence)) :
    occurrence ∈ state.unseen := by
  unfold nextAction? at ha
  cases hu : state.unseen with
  | nil => cases hp : nextPayment? δ state <;> simp [hu, hp] at ha
  | cons head tail =>
      cases hp : nextPayment? δ state with
      | none =>
          simp only [hu, hp] at ha
          injection ha with heq
          cases heq
          simp
      | some pair =>
          simp only [hu, hp] at ha
          split at ha
          · injection ha with heq
            cases heq
            simp
          · simp at ha

private theorem arrival_unseen_eq {state : State Page} {occurrence : Occurrence Page}
    (ha : nextAction? δ state = some (.arrival occurrence)) :
    state.unseen = occurrence :: state.unseen.tail := by
  have hm := arrival_mem_unseen ha
  cases hu : state.unseen with
  | nil => simp [hu] at hm
  | cons head tail =>
      unfold nextAction? at ha
      cases hp : nextPayment? δ state <;> simp only [hu, hp] at ha
      · injection ha with heq; cases heq; simp
      · split at ha
        · injection ha with heq; cases heq; simp
        · simp at ha

theorem step_uniqueIds (input : Instance Page) (state : State Page)
    (action : Action Page) (ha : nextAction? δ state = some action)
    (h : UniqueIds state) : UniqueIds (step input state action) := by
  cases action with
  | arrival occurrence =>
      have hu := arrival_unseen_eq ha
      unfold UniqueIds trackedIds at h ⊢
      simp only [step]
      split
      · rw [hu] at h
        simp only [List.map_append, List.map_cons] at h ⊢
        exact List.Nodup.sublist
          ((List.Sublist.refl _).append
            (List.Sublist.cons _ (List.Sublist.refl _))) h
      · rw [hu] at h
        simpa [List.map_append, List.append_assoc] using h
  | payment time page =>
      unfold UniqueIds trackedIds at h ⊢
      simp only [step, List.flatMap_append, List.flatMap_singleton,
        List.map_append]
      let p : Occurrence Page → Bool := fun o => decide (o.request.page = page)
      have hperm := filter_partition_perm p state.pending
      have hpermAll := (hperm.append_right (state.unseen.map Occurrence.id)).append_left
        ((state.payments.flatMap Payment.served).map Occurrence.id)
      have hold : (((state.payments.flatMap Payment.served).map Occurrence.id) ++
          (state.pending.map Occurrence.id ++ state.unseen.map Occurrence.id)).Nodup := by
        simpa [List.map_append, List.append_assoc] using h
      have hnew := hpermAll.nodup_iff.mpr hold
      have hfilter : state.pending.filter (fun occurrence =>
          decide (occurrence.request.page ≠ page)) = state.pending.filter (fun x => !p x) := by
        apply List.filter_congr
        intro x hx
        simp [p]
      rw [hfilter]
      simpa [p, List.append_assoc] using hnew

private theorem payment_lt_unseen {state : State Page} {time : Time} {page : Page}
    (htime : TimeInvariant state)
    (ha : nextAction? δ state = some (.payment time page))
    {occurrence : Occurrence Page} (ho : occurrence ∈ state.unseen) :
    time < occurrence.request.arrival := by
  unfold nextAction? at ha
  cases hu : state.unseen with
  | nil => simp [hu] at ho
  | cons head tail =>
      cases hp : nextPayment? δ state with
      | none => simp [hu, hp] at ha
      | some pair =>
          rcases pair with ⟨t, p⟩
          simp only [hu, hp] at ha
          split at ha
          · simp at ha
          · injection ha with heq
            cases heq
            have hhead : time < head.request.arrival := lt_of_not_ge (by assumption)
            rw [hu] at ho
            rcases List.mem_cons.mp ho with rfl | htail
            · exact hhead
            · have hchron : head.request.arrival ≤ occurrence.request.arrival := by
                have hc := htime.unseen_chronological
                rw [hu, List.pairwise_cons] at hc
                exact hc.1 occurrence htail
              exact hhead.trans_le hchron

theorem step_strictUnseen (input : Instance Page) (state : State Page)
    (action : Action Page) (htime : TimeInvariant state)
    (ha : nextAction? δ state = some action) (h : StrictUnseen state) :
    StrictUnseen (step input state action) := by
  cases action with
  | arrival occurrence =>
      intro payment hp later hlater
      simp only [step] at hp hlater
      exact h payment hp later (List.mem_of_mem_tail hlater)
  | payment time page =>
      intro payment hp occurrence ho
      simp only [step, List.mem_append, List.mem_singleton] at hp ho
      rcases hp with hold | rfl
      · exact h payment hold occurrence ho
      · exact payment_lt_unseen htime ha ho

theorem step_pendingSinceEviction (input : Instance Page) (valid : input.Valid)
    (state : State Page) (action : Action Page)
    (hfresh : FreshQueue input state)
    (hstrict : StrictUnseen state) (hpending : PendingSinceEviction input state)
    (haction : nextAction? δ state = some action) :
    PendingSinceEviction input (step input state action) := by
  cases action with
  | arrival occurrence =>
      have hunseen : occurrence ∈ state.unseen := arrival_mem_unseen haction
      simp only [step]
      split
      · intro candidate hcand previous hp hpage
        exact hpending candidate hcand previous hp hpage
      · rename_i hmiss
        intro candidate hcand previous hp hpage
        rcases List.mem_append.mp hcand with hold | hnew
        · exact hpending candidate hold previous hp hpage
        · have heq : candidate = occurrence := by simpa using hnew
          subst candidate
          have hlt : previous + input.cacheSize < state.payments.length := by
            by_contra hn
            have hnear : state.payments.length ≤ previous + input.cacheSize :=
              Nat.le_of_not_gt hn
            have hmem : state.payments[previous].page ∈
                recentPages input.cacheSize state.payments := by
              have := page_mem_recentPages_between valid.positiveCapacity
                state.payments (le_rfl) hp hnear
              simpa [List.take_length] using this
            have hqueue : state.queue = recentPages input.cacheSize state.payments :=
              hfresh.recent
            have : occurrence.request.page ∈ state.queue := by
              rw [hqueue, ← hpage]
              exact hmem
            exact hmiss this
          refine ⟨hlt, ?_⟩
          have hs := hstrict state.payments[previous + input.cacheSize]
            (List.getElem_mem (l := state.payments)
              (n := previous + input.cacheSize) hlt) occurrence hunseen
          simpa [List.getElem?_eq_getElem hlt] using hs
  | payment time page =>
      intro occurrence hoccur previous hp hpage
      simp only [step] at hoccur hp ⊢
      have hold := (List.mem_filter.mp hoccur)
      have hpold : previous < state.payments.length := by
        simp only [List.length_append, List.length_singleton] at hp
        by_contra hn
        have heq : previous = state.payments.length := by omega
        subst previous
        have hne : occurrence.request.page ≠ page := of_decide_eq_true hold.2
        have : page = occurrence.request.page := by
          simpa [step] using hpage
        exact hne this.symm
      have hpageOld : state.payments[previous].page = occurrence.request.page := by
        simpa [step, List.getElem_append_left hpold] using hpage
      obtain ⟨hev, htime⟩ := hpending occurrence hold.1 previous hpold hpageOld
      constructor
      · simp only [List.length_append, List.length_singleton]
        omega
      · change ((state.payments ++ [_])[previous + input.cacheSize]?).any
          (fun payment => payment.time < occurrence.request.arrival)
        rw [List.getElem?_append_left hev]
        exact htime

theorem step_validBatchLowerBounds (input : Instance Page) (state : State Page)
    (action : Action Page) (hpending : PendingSinceEviction input state)
    (hbatches : ValidBatchLowerBounds input state) :
    ValidBatchLowerBounds input (step input state action) := by
  cases action with
  | arrival occurrence => simpa [step, ValidBatchLowerBounds] using hbatches
  | payment time page =>
      intro index hindex occurrence hoccur previous hprevious hpage
      simp only [step, List.length_append, List.length_singleton] at hindex
      by_cases hi : index < state.payments.length
      · have hoccurOld : occurrence ∈ state.payments[index].served := by
          simpa [step, List.getElem_append_left hi] using hoccur
        have hpold : previous < state.payments.length := hprevious.trans hi
        have hpageOld : state.payments[previous].page = state.payments[index].page := by
          simpa [step, List.getElem_append_left hi,
            List.getElem_append_left hpold] using hpage
        obtain ⟨hb, ht⟩ := hbatches index hi occurrence hoccurOld previous hprevious hpageOld
        refine ⟨hb, ?_⟩
        change ((state.payments ++ [_])[previous + input.cacheSize]?).any
          (fun payment => payment.time < occurrence.request.arrival)
        rw [List.getElem?_append_left (hb.trans hi)]
        exact ht
      · have hieq : index = state.payments.length := by omega
        subst index
        have hoccurNew : occurrence ∈
            state.pending.filter (fun occurrence => occurrence.request.page = page) := by
          simpa [step] using hoccur
        have hpold : previous < state.payments.length := hprevious
        have hpageOld : state.payments[previous].page = page := by
          simpa [step, List.getElem_append_left hpold] using hpage
        have hm : occurrence ∈ state.pending := (List.mem_filter.mp hoccurNew).1
        have hsame : state.payments[previous].page = occurrence.request.page := by
          exact hpageOld.trans (of_decide_eq_true (List.mem_filter.mp hoccurNew).2).symm
        obtain ⟨hb, ht⟩ := hpending occurrence hm previous hpold hsame
        refine ⟨hb, ?_⟩
        change ((state.payments ++ [_])[previous + input.cacheSize]?).any
          (fun payment => payment.time < occurrence.request.arrival)
        rw [List.getElem?_append_left hb]
        exact ht

theorem run_lowerBounds (input : Instance Page) (valid : input.Valid) : ∀ fuel state,
    TimeInvariant state → BelowThreshold δ state → FreshQueue input state →
      CacheInvariant input state → StrictUnseen state →
      PendingSinceEviction input state → ValidBatchLowerBounds input state →
      ValidBatchLowerBounds input (run δ input fuel state) := by
  intro fuel
  induction fuel with
  | zero => exact fun _ _ _ _ _ _ _ h => h
  | succ fuel ih =>
      intro state htime hbelow hfresh hcache hstrict hpending hbatches
      rw [run]
      cases ha : nextAction? δ state with
      | none => exact hbatches
      | some action =>
          exact ih _
            (step_timeInvariant input state action htime ha)
            (step_belowThreshold input state action hbelow ha)
            (step_freshQueue input valid state action hfresh hcache ha)
            (step_cacheInvariant input valid state action hcache ha)
            (step_strictUnseen input state action htime ha hstrict)
            (step_pendingSinceEviction input valid state action hfresh
              hstrict hpending ha)
            (step_validBatchLowerBounds input state action hpending hbatches)

theorem final_validBatchLowerBounds (input : Instance Page) (valid : input.Valid) :
    ValidBatchLowerBounds input (run δ input (2 * input.requests.length) (initialState input)) := by
  exact run_lowerBounds input valid _ _
    (initial_timeInvariant input valid) (initial_belowThreshold input)
    (initial_freshQueue input) (initial_cacheInvariant input)
    (initial_strictUnseen input)
    (by simp [PendingSinceEviction, initialState])
    (by simp [ValidBatchLowerBounds, initialState])

theorem step_history (input : Instance Page) (state : State Page)
    (action : Action Page) (htime : TimeInvariant state)
    (hpending : PendingArrived state)
    (hbatches : ValidBatches state) (haction : nextAction? δ state = some action) :
    PendingArrived (step input state action) ∧ ValidBatches (step input state action) := by
  cases action with
  | arrival occurrence =>
      have hnow : state.now ≤ occurrence.request.arrival :=
        htime.now_before_unseen occurrence (arrival_mem_unseen haction)
      constructor
      · intro candidate hmem
        simp only [step] at hmem ⊢
        split at hmem
        · exact (hpending candidate hmem).trans hnow
        · simp only [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hold | rfl
          · exact (hpending candidate hold).trans hnow
          · exact le_rfl
      · simpa [ValidBatches, step] using hbatches
  | payment time page =>
      have hselected := nextAction_payment_selected haction
      have hpagePending := pending_of_mem_pendingPages
        (nextPayment_mem_pendingPages hselected)
      have hnow : state.now ≤ time := by
        rw [← nextPayment_time_eq hselected]
        exact thresholdTime_ge_now state page hpagePending
      constructor
      · intro occurrence hmem
        exact (hpending occurrence (List.mem_filter.mp hmem).1).trans hnow
      · intro payment hpayment occurrence hserved
        simp only [step, List.mem_append, List.mem_singleton] at hpayment
        rcases hpayment with hold | rfl
        · exact hbatches payment hold occurrence hserved
        · have hm := List.mem_filter.mp hserved
          exact ⟨of_decide_eq_true hm.2, (hpending occurrence hm.1).trans hnow⟩

theorem run_history (input : Instance Page) : ∀ fuel state,
    TimeInvariant state → BelowThreshold δ state → PendingArrived state →
      ValidBatches state →
    PendingArrived (run δ input fuel state) ∧ ValidBatches (run δ input fuel state) := by
  intro fuel
  induction fuel with
  | zero => exact fun _ _ _ hp hb => ⟨hp, hb⟩
  | succ fuel ih =>
      intro state ht hb hp hv
      rw [run]
      cases ha : nextAction? δ state with
      | none => exact ⟨hp, hv⟩
      | some action =>
          have hh := step_history input state action ht hp hv ha
          exact ih _ (step_timeInvariant input state action ht ha)
            (step_belowThreshold input state action hb ha) hh.1 hh.2

theorem final_validBatches (input : Instance Page) (valid : input.Valid) :
    ValidBatches (run δ input (2 * input.requests.length) (initialState input)) := by
  exact (run_history input _ _ (initial_timeInvariant input valid)
    (initial_belowThreshold input) (by simp [PendingArrived, initialState])
    (by simp [ValidBatches, initialState])).2

theorem step_authentic (input : Instance Page) (state : State Page)
    (action : Action Page) (ha : nextAction? δ state = some action)
    (h : Authentic input state) : Authentic input (step input state action) := by
  cases action with
  | arrival occurrence =>
      have hm := h.1 occurrence (arrival_mem_unseen ha)
      constructor
      · intro o ho
        exact h.1 o (by
          simp only [step] at ho
          exact List.mem_of_mem_tail ho)
      · constructor
        · intro o ho
          simp only [step] at ho
          split at ho
          · exact h.2.1 o ho
          · rcases List.mem_append.mp ho with hold | hnew
            · exact h.2.1 o hold
            · have heq : o = occurrence := by simpa using hnew
              subst o
              exact hm
        · simpa [step] using h.2.2
  | payment time page =>
      constructor
      · simpa [step] using h.1
      · constructor
        · intro o ho
          exact h.2.1 o (List.mem_filter.mp ho).1
        · intro p hp o ho
          simp only [step, List.mem_append, List.mem_singleton] at hp
          rcases hp with hold | rfl
          · exact h.2.2 p hold o ho
          · exact h.2.1 o (List.mem_filter.mp ho).1

theorem run_authentic (input : Instance Page) : ∀ fuel state,
    Authentic input state → Authentic input (run δ input fuel state) := by
  intro fuel
  induction fuel with
  | zero => exact fun _ h => h
  | succ fuel ih =>
      intro state h
      rw [run]
      cases ha : nextAction? δ state with
      | none => exact h
      | some action => exact ih _ (step_authentic input state action ha h)

theorem final_authentic (input : Instance Page) : Authentic input (run δ input (2 * input.requests.length) (initialState input)) := by
  apply run_authentic
  simp [Authentic, initialState]

theorem run_uniqueIds (input : Instance Page) : ∀ fuel state,
    UniqueIds state → UniqueIds (run δ input fuel state) := by
  intro fuel
  induction fuel with
  | zero => exact fun _ h => h
  | succ fuel ih =>
      intro state h
      rw [run]
      cases ha : nextAction? δ state with
      | none => exact h
      | some action => exact ih _ (step_uniqueIds input state action ha h)

theorem final_uniqueIds (input : Instance Page) : UniqueIds (run δ input (2 * input.requests.length) (initialState input)) := by
  exact run_uniqueIds input _ _ (initial_uniqueIds input)

/-- Identifiers are pairwise distinct across the whole completed payment log:
no occurrence is served twice, in one batch or in two. -/
theorem final_servedIds_nodup (input : Instance Page) :
    (((run δ input (2 * input.requests.length)
      (initialState input)).payments.flatMap Payment.served).map Occurrence.id).Nodup := by
  have h := final_uniqueIds (δ := δ) input
  unfold UniqueIds trackedIds at h
  exact h.sublist (by simp)

end History

end
end PagingWithDelay.FIFO
