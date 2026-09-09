import PagingWithDelay.EventLoop.CacheInvariant
import PagingWithDelay.EventLoop.TemporalInvariant

/-!
# Freshness of the FIFO payment log

Every payment fetches a page that is absent from the queue it replaces.  This
is what turns the abstract replay `recentPages` into the paper's closed form —
the suffix of the last `min(k, M)` fetched pages — and what yields the eviction
spacing `i + k < j` between two payments for the same page.
-/


namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page] {δ : Cost}

/-- Every payment page is absent from the queue obtained from the preceding
payments.  This is the exact history property used by the FIFO suffix proof. -/
inductive FreshPayments (capacity : ℕ) : List (Payment Page) → Prop
  | nil : FreshPayments capacity []
  | snoc {payments : List (Payment Page)} (h : FreshPayments capacity payments)
      (payment : Payment Page)
      (fresh : payment.page ∉ recentPages capacity payments) :
      (coherent : payment.queueAfter = recentPages capacity (payments ++ [payment])) →
      FreshPayments capacity (payments ++ [payment])

theorem FreshPayments.fresh_at {capacity : ℕ} {payments : List (Payment Page)}
    (h : FreshPayments capacity payments) (index : ℕ) (hindex : index < payments.length) :
    payments[index].page ∉ recentPages capacity (payments.take index) := by
  induction h with
  | nil => simp at hindex
  | @snoc previous hp payment hfresh coherent ih =>
      simp only [List.length_append, List.length_singleton] at hindex
      by_cases hlt : index < previous.length
      · have hget : (previous ++ [payment])[index] = previous[index] := by
          exact List.getElem_append_left hlt
        have htake : (previous ++ [payment]).take index = previous.take index := by
          rw [List.take_append_of_le_length]
          omega
        rw [hget, htake]
        exact ih hlt
      · have heq : index = previous.length := by omega
        subst index
        simpa using hfresh

theorem FreshPayments.queueAfter_at {capacity : ℕ} {payments : List (Payment Page)}
    (h : FreshPayments capacity payments) (index : ℕ) (hindex : index < payments.length) :
    payments[index].queueAfter = recentPages capacity (payments.take (index + 1)) := by
  induction h with
  | nil => simp at hindex
  | @snoc previous hp payment hfresh coherent ih =>
      simp only [List.length_append, List.length_singleton] at hindex
      by_cases hlt : index < previous.length
      · rw [List.getElem_append_left hlt, List.take_append_of_le_length]
        · exact ih hlt
        · omega
      · have heq : index = previous.length := by omega
        subst index
        rw [show previous.length + 1 = (previous ++ [payment]).length by simp,
          List.take_length]
        simpa using coherent

/-- Execution invariant combining the suffix replay with freshness of every
payment at the instant it was made. -/
structure FreshQueue (input : Instance Page) (state : State Page) : Prop where
  recent : RecentQueue input state
  fresh : FreshPayments input.cacheSize state.payments

theorem initial_freshQueue (input : Instance Page) :
    FreshQueue input (initialState input) := by
  exact ⟨initial_recentQueue input, .nil⟩

theorem step_freshQueue (input : Instance Page) (valid : input.Valid)
    (state : State Page) (action : Action Page)
    (hfq : FreshQueue input state) (hcache : CacheInvariant input state)
    (haction : nextAction? δ state = some action) :
    FreshQueue input (step input state action) := by
  constructor
  · exact step_recentQueue input valid state action hfq.recent hcache haction
  · cases action with
    | arrival occurrence => simpa [step] using hfq.fresh
    | payment time page =>
      have hselected : nextPayment? δ state = some (time, page) :=
        nextAction_payment_selected haction
      obtain ⟨occurrence, hpending, hpage⟩ :=
        pending_of_mem_pendingPages (nextPayment_mem_pendingPages hselected)
      have hmiss : page ∉ state.queue := by
        rw [← hpage]
        exact hcache.pending_miss occurrence hpending
      apply FreshPayments.snoc hfq.fresh
      have hrecent := hfq.recent
      unfold RecentQueue at hrecent
      rw [← hrecent]
      exact hmiss
      · have hrecent := hfq.recent
        unfold RecentQueue at hrecent
        exact recentPages_append input.cacheSize state.payments state.queue
          { time := time, page := page,
            served := state.pending.filter fun occurrence => occurrence.request.page = page,
            queueAfter := insertPage input.cacheSize state.queue page } hrecent

theorem run_freshQueue (input : Instance Page) (valid : input.Valid) :
    ∀ fuel state, FreshQueue input state → CacheInvariant input state →
      FreshQueue input (run δ input fuel state) := by
  intro fuel
  induction fuel with
  | zero => exact fun _ h _ => h
  | succ fuel ih =>
      intro state hfq hcache
      rw [run]
      cases ha : nextAction? δ state with
      | none => exact hfq
      | some action =>
          exact ih _ (step_freshQueue input valid state action hfq hcache ha)
            (step_cacheInvariant input valid state action hcache ha)

theorem final_freshPayments (input : Instance Page) (valid : input.Valid) :
    FreshPayments input.cacheSize
      (run δ input (2 * input.requests.length) (initialState input)).payments := by
  exact (run_freshQueue input valid _ _ (initial_freshQueue input)
    (initial_cacheInvariant input)).fresh

omit [DecidableEq Page] in private theorem drop_succ_eq_tail
    (n : ℕ) (xs : List Page) :
    xs.drop (n + 1) = (xs.drop n).tail := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
      cases n with
      | zero => rfl
      | succ n => exact ih n

omit [DecidableEq Page] in private theorem insertPage_drop_suffix
    (capacity : ℕ) (hpositive : 0 < capacity)
    (pages : List Page) (page : Page) :
    insertPage capacity (pages.drop (pages.length - capacity)) page =
      (pages ++ [page]).drop ((pages ++ [page]).length - capacity) := by
  unfold insertPage
  simp only [List.length_drop, List.length_append, List.length_singleton]
  by_cases hn : pages.length < capacity
  · have hsub : pages.length - capacity = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hn)
    have hsucc : pages.length + 1 ≤ capacity := hn
    simp [hsub, Nat.sub_eq_zero_of_le hsucc, hn]
  · have hcap : capacity ≤ pages.length := Nat.le_of_not_gt hn
    have hlen : pages.length - (pages.length - capacity) = capacity := by omega
    simp only [hlen, lt_self_iff_false, ↓reduceIte]
    have hindex : pages.length + 1 - capacity = (pages.length - capacity) + 1 := by
      omega
    rw [hindex, drop_succ_eq_tail]
    have hdrop : pages.length - capacity ≤ pages.length := Nat.sub_le _ _
    rw [List.drop_append_of_le_length (l₂ := [page]) hdrop]
    have hnonempty : pages.drop (pages.length - capacity) ≠ [] := by
      intro hempty
      have : (pages.drop (pages.length - capacity)).length = capacity := by
        simp only [List.length_drop]
        exact hlen
      rw [hempty] at this
      simp at this
      omega
    cases htail : pages.drop (pages.length - capacity) with
    | nil => exact (hnonempty htail).elim
    | cons head tail => rfl

/-- Concrete FIFO replay is exactly the suffix of at most `capacity` payment
pages.  This is the closed form used by the paper's cache invariant. -/
theorem recentPages_eq_lastPaymentPages (capacity : ℕ) (hpositive : 0 < capacity)
    (payments : List (Payment Page)) :
    recentPages capacity payments = lastPaymentPages capacity payments := by
  induction payments using List.reverseRecOn with
  | nil => simp [recentPages, lastPaymentPages]
  | append_singleton payments payment ih =>
      rw [← recentPages_append capacity payments (recentPages capacity payments)
        payment rfl, ih]
      unfold lastPaymentPages
      simp only [List.map_append, List.map_singleton]
      exact insertPage_drop_suffix capacity hpositive
        (payments.map Payment.page) payment.page

theorem recentPages_take_add (capacity start : ℕ) (hpositive : 0 < capacity)
    (payments : List (Payment Page)) (hbound : start + capacity ≤ payments.length) :
    recentPages capacity (payments.take (start + capacity)) =
      ((payments.drop start).take capacity).map Payment.page := by
  rw [recentPages_eq_lastPaymentPages capacity hpositive]
  unfold lastPaymentPages
  simp only [List.map_take, List.length_take, List.length_map,
    Nat.min_eq_left hbound, List.map_drop]
  rw [List.drop_take]
  simp

theorem page_mem_recentPages_between {capacity i j : ℕ} (hpositive : 0 < capacity)
    (payments : List (Payment Page)) (hj : j ≤ payments.length)
    (hij : i < j) (hnear : j ≤ i + capacity) :
    payments[i].page ∈ recentPages capacity (payments.take j) := by
  rw [recentPages_eq_lastPaymentPages capacity hpositive]
  unfold lastPaymentPages
  simp only [List.map_take, List.length_take, List.length_map, Nat.min_eq_left hj]
  let d := j - capacity
  have hdle : d ≤ i := by dsimp [d]; omega
  have hi : i < payments.length := hij.trans_le hj
  have hidx : i - d <
      (List.drop d (List.take j (List.map Payment.page payments))).length := by
    simp only [List.length_drop, List.length_take, List.length_map,
      Nat.min_eq_left hj]
    omega
  have hm := List.getElem_mem
    (l := List.drop d (List.take j (List.map Payment.page payments)))
    (n := i - d) hidx
  convert hm using 1
  all_goals simp [List.getElem_drop, d, hdle]

/-- Two actual payments of the same page are separated by more than the cache
capacity.  Equivalently, the earlier page is evicted by payment `i+k` before
it can be fetched again. -/
theorem samePage_spacing (input : Instance Page) (valid : input.Valid)
    {i j : ℕ}
    (hi : i < (run δ input (2 * input.requests.length) (initialState input)).payments.length)
    (hj : j < (run δ input (2 * input.requests.length) (initialState input)).payments.length)
    (hij : i < j)
    (hpage :
      (run δ input (2 * input.requests.length) (initialState input)).payments[i].page =
      (run δ input (2 * input.requests.length) (initialState input)).payments[j].page) :
    i + input.cacheSize < j := by
  let payments := (run δ input (2 * input.requests.length) (initialState input)).payments
  by_contra hnot
  have hnear : j ≤ i + input.cacheSize := Nat.le_of_not_gt hnot
  have hmem : payments[i].page ∈ recentPages input.cacheSize (payments.take j) :=
    page_mem_recentPages_between valid.positiveCapacity payments
      (Nat.le_of_lt hj) hij hnear
  have hfresh := (final_freshPayments input valid).fresh_at j hj
  apply hfresh
  rw [← hpage]
  exact hmem

end PagingWithDelay.FIFO
