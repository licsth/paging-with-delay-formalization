import PagingWithDelay.EventLoop.StateInvariants

/-!
# FIFO cache invariant

This file begins the formalization of Lemma 3.1 in `fifo-upper-bound.tex`.
-/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page] {δ : Cost}

/-- Replay the concrete FIFO insertion rule on a payment history.  For an
arbitrary list this is deliberately not identified with its last `capacity`
pages: that identification also needs the execution invariant saying that a
payment page is absent from the current queue. -/
def recentPages (capacity : ℕ) (payments : List (Payment Page)) : List Page :=
  payments.foldl (fun queue payment =>
    insertPage capacity queue payment.page) []

/-- Closed form used in the paper: the suffix of fetched pages of length at
most the cache capacity. -/
def lastPaymentPages (capacity : ℕ) (payments : List (Payment Page)) : List Page :=
  let pages := payments.map Payment.page
  pages.drop (pages.length - capacity)

/-- The paper's cache invariant, stated for an internal execution state. -/
def RecentQueue (input : Instance Page) (state : State Page) : Prop :=
  state.queue = recentPages input.cacheSize state.payments

theorem initial_recentQueue (input : Instance Page) :
    RecentQueue input (initialState input) := by
  simp [RecentQueue, recentPages, initialState]

/-- Appending a payment commutes with replaying the concrete replacement rule. -/
theorem recentPages_append (capacity : ℕ) (payments : List (Payment Page))
    (queue : List Page) (newPayment : Payment Page)
    (hqueue : queue = recentPages capacity payments) :
    insertPage capacity queue newPayment.page =
      recentPages capacity (payments ++ [newPayment]) := by
  subst queue
  simp [recentPages]

/-- The replayed queue never exceeds the cache capacity: it holds the last
`min(capacity, number of payments)` fetched pages. -/
theorem recentPages_length (capacity : ℕ) (hpositive : 0 < capacity) :
    ∀ payments : List (Payment Page),
      (recentPages capacity payments).length = min capacity payments.length := by
  intro payments
  induction payments using List.reverseRecOn with
  | nil => simp [recentPages]
  | append_singleton payments newPayment ih =>
      rw [← recentPages_append capacity payments (recentPages capacity payments)
        newPayment rfl]
      unfold insertPage
      simp only [ih, List.length_append, List.length_singleton]
      split <;> simp_all <;> omega

/-- One selected FIFO action preserves the recent-payments description of the
queue. -/
theorem step_recentQueue (input : Instance Page) (_valid : input.Valid)
    (state : State Page) (action : Action Page)
    (hrecent : RecentQueue input state)
    (_hcache : CacheInvariant input state)
    (_haction : nextAction? δ state = some action) :
    RecentQueue input (step input state action) := by
  cases action with
  | arrival occurrence =>
      simpa [RecentQueue, step] using hrecent
  | payment time page =>
      unfold RecentQueue at hrecent ⊢
      simp only [step]
      exact recentPages_append input.cacheSize state.payments state.queue
        { time := time, page := page,
          served := state.pending.filter fun occurrence => occurrence.request.page = page,
          queueAfter := insertPage input.cacheSize state.queue page } hrecent

end PagingWithDelay.FIFO
