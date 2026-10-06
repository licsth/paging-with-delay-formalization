import Proofs.EventLoop.FreshQueue
import Proofs.EventLoop.PaymentOrder
import Proofs.EventLoop.OccurrencePartition

/-!
# History invariants of the FIFO run

Bookkeeping facts about the payment log that the event loop builds: batches
record occurrences of the page they fetch, arriving no later than the payment;
occurrence identifiers are never duplicated; and a pending request for a page that FIFO has evicted —
whether it was fetched by an earlier payment or held from the start — arrived
after that eviction.

All of these are invariants of the reachable states (`Reachable`), preserved
by `step`.  None depends on the competitive analysis.
-/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page] {trigger : Trigger}

noncomputable section

namespace History

open FIFO

def PendingArrived (state : State Page) : Prop :=
  ∀ occurrence ∈ state.pending, occurrence.request.arrival ≤ state.now

def ValidBatches (state : State Page) : Prop :=
  ∀ payment ∈ state.payments, ∀ occurrence ∈ payment.served,
    occurrence.request.page = payment.page ∧
      occurrence.request.arrival ≤ payment.time

def trackedIds (state : State Page) : List ℕ :=
  ((state.payments.flatMap Payment.served) ++ state.pending ++ state.unseen).map Occurrence.id

def UniqueIds (state : State Page) : Prop := (trackedIds state).Nodup

def StrictUnseen (state : State Page) : Prop :=
  ∀ payment ∈ state.payments, ∀ occurrence ∈ state.unseen,
    payment.time < occurrence.request.arrival

/-- The initial queue followed by the fetched pages.  On a instance its
entry at position `j` is the page FIFO evicts at payment `j`: the initial queue
is evicted front to back by the first `k` payments, and the page fetched by
payment `i` is evicted by payment `i + k`. -/
def evictionOrder (input : Instance Page) (payments : List (Payment Page)) : List Page :=
  input.initialCache ++ payments.map Payment.page

@[simp] theorem evictionOrder_length (input : Instance Page) (payments : List (Payment Page)) :
    (evictionOrder input payments).length = input.initialCache.length + payments.length := by
  simp [evictionOrder]

theorem evictionOrder_append (input : Instance Page) (payments : List (Payment Page))
    (payment : Payment Page) :
    evictionOrder input (payments ++ [payment]) =
      evictionOrder input payments ++ [payment.page] := by
  simp [evictionOrder]

theorem evictionOrder_getElem_initial (input : Instance Page) (payments : List (Payment Page))
    {p : ℕ} (hp : p < input.initialCache.length) :
    (evictionOrder input payments)[p]'(by simp; omega) = input.initialCache[p] :=
  List.getElem_append_left hp

theorem evictionOrder_getElem_payment (input : Instance Page) (payments : List (Payment Page))
    {i : ℕ} (hi : i < payments.length) :
    (evictionOrder input payments)[input.initialCache.length + i]'(by simp; omega) =
      payments[i].page := by
  unfold evictionOrder
  rw [List.getElem_append_right (by omega)]
  simp

/-- A pending request for a page that FIFO has evicted arrived strictly after
that eviction: the page at position `j` of the eviction order is evicted by
payment `j`.  Indices are relative to the payment prefix recorded in `state`. -/
def PendingSinceEviction (input : Instance Page) (state : State Page) : Prop :=
  ∀ occurrence ∈ state.pending,
    ∀ j (hj : j < (evictionOrder input state.payments).length),
      (evictionOrder input state.payments)[j] = occurrence.request.page →
        j < state.payments.length ∧
          (state.payments[j]?).any
            (fun payment => payment.time < occurrence.request.arrival)

/-- The already recorded batches satisfy the lower endpoint of their payment
window: a request served by payment `index` arrived after every eviction of
its page preceding that payment.  Positions `j < initialCache.length + index`
of the eviction order are exactly the initial queue and the payments before
`index`. -/
def ValidBatchLowerBounds (input : Instance Page) (state : State Page) : Prop :=
  ∀ index (hindex : index < state.payments.length),
    ∀ occurrence ∈ state.payments[index].served,
      ∀ j (hj : j < input.initialCache.length + index),
        (evictionOrder input state.payments)[j]'(by simp; omega) =
            state.payments[index].page →
          j < index ∧
            (state.payments[j]?).any
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

theorem step_uniqueIds (input : Instance Page) (state : State Page)
    (action : Action Page) (ha : nextAction? trigger state = some action)
    (h : UniqueIds state) : UniqueIds (step input state action) := by
  cases action with
  | arrival occurrence =>
      have hu := (nextAction_arrival ha).1
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
      have hperm := (((List.filter_append_perm
        (fun o : Occurrence Page => decide (o.request.page = page)) state.pending).map
          Occurrence.id).append_right (state.unseen.map Occurrence.id)).append_left
        ((state.payments.flatMap Payment.served).map Occurrence.id)
      simpa [step, List.append_assoc] using hperm.nodup_iff.2 (by simpa using h)

theorem step_strictUnseen (input : Instance Page) (state : State Page)
    (action : Action Page) (htime : TimeInvariant state)
    (ha : nextAction? trigger state = some action) (h : StrictUnseen state) :
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

theorem step_pendingSinceEviction (input : Instance Page)
    (state : State Page) (action : Action Page)
    (hfresh : FreshQueue input state)
    (hstrict : StrictUnseen state) (hpending : PendingSinceEviction input state)
    (haction : nextAction? trigger state = some action) :
    PendingSinceEviction input (step input state action) := by
  cases action with
  | arrival occurrence =>
      have hunseen : occurrence ∈ state.unseen := arrival_mem_unseen haction
      intro candidate hcand j hj hpage
      simp only [step] at hcand hj hpage ⊢
      split at hcand
      · exact hpending candidate hcand j hj hpage
      · rename_i hmiss
        rcases List.mem_append.mp hcand with hold | hnew
        · exact hpending candidate hold j hj hpage
        · have heq : candidate = occurrence := by simpa using hnew
          subst candidate
          have hlt : j < state.payments.length := by
            by_contra hn
            have hnear : input.initialCache.length + state.payments.length ≤
                j + input.cacheSize := by
              have := input.initialCache_full
              omega
            have hmem : (evictionOrder input state.payments)[j] ∈
                recentPages input.cacheSize input.initialCache state.payments :=
              getElem_mem_recentPages input.positiveCapacity input.initialCache
                input.initialCache_full.le state.payments hj hnear
            have hqueue : state.queue =
                recentPages input.cacheSize input.initialCache state.payments :=
              hfresh.recent
            have : occurrence.request.page ∈ state.queue := by
              rw [hqueue, ← hpage]
              exact hmem
            exact hmiss this
          refine ⟨hlt, ?_⟩
          have hs := hstrict state.payments[j]
            (List.getElem_mem (l := state.payments) (n := j) hlt) occurrence hunseen
          simpa [List.getElem?_eq_getElem hlt] using hs
  | payment time page =>
      intro occurrence hoccur j hj hpage
      simp only [step] at hoccur hj hpage ⊢
      have hold := (List.mem_filter.mp hoccur)
      simp only [evictionOrder_append, List.length_append, List.length_singleton] at hj hpage
      have hjold : j < (evictionOrder input state.payments).length := by
        by_contra hn
        have heq : j = (evictionOrder input state.payments).length := by omega
        have hne : occurrence.request.page ≠ page := of_decide_eq_true hold.2
        rw [List.getElem_append_right (by omega)] at hpage
        simp [heq] at hpage
        exact hne hpage.symm
      have hpageOld : (evictionOrder input state.payments)[j] = occurrence.request.page := by
        rw [← hpage, List.getElem_append_left hjold]
      obtain ⟨hev, htime⟩ := hpending occurrence hold.1 j hjold hpageOld
      constructor
      · simp only [List.length_append, List.length_singleton]
        omega
      · change ((state.payments ++ [_])[j]?).any
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
      intro index hindex occurrence hoccur j hj hpage
      simp only [step, List.length_append, List.length_singleton] at hindex hpage
      simp only [evictionOrder_append] at hpage
      rw [List.getElem_append_left (by simp; omega)] at hpage
      by_cases hi : index < state.payments.length
      · have hoccurOld : occurrence ∈ state.payments[index].served := by
          simpa [step, List.getElem_append_left hi] using hoccur
        have hpageOld : (evictionOrder input state.payments)[j]'(by simp; omega) =
            state.payments[index].page := by
          rw [hpage, List.getElem_append_left hi]
        obtain ⟨hb, ht⟩ := hbatches index hi occurrence hoccurOld j hj hpageOld
        refine ⟨hb, ?_⟩
        change ((state.payments ++ [_])[j]?).any
          (fun payment => payment.time < occurrence.request.arrival)
        rw [List.getElem?_append_left (hb.trans hi)]
        exact ht
      · have hieq : index = state.payments.length := by omega
        subst index
        have hoccurNew : occurrence ∈
            state.pending.filter (fun occurrence => occurrence.request.page = page) := by
          simpa [step] using hoccur
        have hm : occurrence ∈ state.pending := (List.mem_filter.mp hoccurNew).1
        have hsame : (evictionOrder input state.payments)[j]'(by simp; omega) =
            occurrence.request.page := by
          rw [hpage, List.getElem_append_right (by omega)]
          simp only [Nat.sub_self, List.getElem_singleton]
          exact (of_decide_eq_true (List.mem_filter.mp hoccurNew).2).symm
        obtain ⟨hb, ht⟩ := hpending occurrence hm j (by simp; omega) hsame
        refine ⟨hb, ?_⟩
        change ((state.payments ++ [_])[j]?).any
          (fun payment => payment.time < occurrence.request.arrival)
        rw [List.getElem?_append_left hb]
        exact ht

theorem step_history (input : Instance Page) (state : State Page)
    (action : Action Page) (htime : TimeInvariant state)
    (hpending : PendingArrived state)
    (hbatches : ValidBatches state) (haction : nextAction? trigger state = some action) :
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
      have hnow := nextPayment_now_le (nextAction_payment_selected haction)
      constructor
      · intro occurrence hmem
        exact (hpending occurrence (List.mem_filter.mp hmem).1).trans hnow
      · intro payment hpayment occurrence hserved
        simp only [step, List.mem_append, List.mem_singleton] at hpayment
        rcases hpayment with hold | rfl
        · exact hbatches payment hold occurrence hserved
        · have hm := List.mem_filter.mp hserved
          exact ⟨of_decide_eq_true hm.2, (hpending occurrence hm.1).trans hnow⟩

end History

open History

theorem Reachable.strictUnseen {input : Instance Page} {state : State Page}
    (h : Reachable trigger input state) : StrictUnseen state := by
  induction h with
  | initial => exact initial_strictUnseen input
  | step hr ha ih => exact step_strictUnseen input _ _ hr.timeInvariant ha ih

theorem Reachable.pendingSinceEviction {input : Instance Page} {state : State Page}
    (h : Reachable trigger input state) : PendingSinceEviction input state := by
  induction h with
  | initial => simp [PendingSinceEviction, initialState]
  | step hr ha ih =>
      exact step_pendingSinceEviction input _ _ hr.freshQueue hr.strictUnseen ih ha

theorem Reachable.validBatchLowerBounds {input : Instance Page} {state : State Page}
    (h : Reachable trigger input state) : ValidBatchLowerBounds input state := by
  induction h with
  | initial => simp [ValidBatchLowerBounds, initialState]
  | step hr _ ih => exact step_validBatchLowerBounds input _ _ hr.pendingSinceEviction ih

theorem Reachable.history {input : Instance Page} {state : State Page}
    (h : Reachable trigger input state) : PendingArrived state ∧ ValidBatches state := by
  induction h with
  | initial => simp [PendingArrived, ValidBatches, initialState]
  | step hr ha ih => exact step_history input _ _ hr.timeInvariant ih.1 ih.2 ha

theorem Reachable.uniqueIds {input : Instance Page} {state : State Page}
    (h : Reachable trigger input state) : UniqueIds state := by
  induction h with
  | initial => exact initial_uniqueIds input
  | step _ ha ih => exact step_uniqueIds input _ _ ha ih

namespace History

theorem final_validBatchLowerBounds (input : Instance Page) :
    ValidBatchLowerBounds input (run trigger input (2 * input.requests.length) (initialState input)) :=
  (reachable_final input).validBatchLowerBounds

theorem final_validBatches (input : Instance Page) :
    ValidBatches (run trigger input (2 * input.requests.length) (initialState input)) :=
  (reachable_final input).history.2

/-- Identifiers are pairwise distinct across the whole completed payment log:
no occurrence is served twice, in one batch or in two. -/
theorem final_servedIds_nodup (input : Instance Page) :
    (((run trigger input (2 * input.requests.length)
      (initialState input)).payments.flatMap Payment.served).map Occurrence.id).Nodup :=
  (reachable_final (trigger := trigger) input).uniqueIds.sublist (by simp [trackedIds])

end History

end
end PagingWithDelay.FIFO
