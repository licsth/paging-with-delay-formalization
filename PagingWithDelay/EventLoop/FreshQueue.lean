import PagingWithDelay.EventLoop.CacheInvariant
import PagingWithDelay.EventLoop.TemporalInvariant

/-!
# Freshness of the FIFO payment log

Every payment fetches a page that is absent from the queue it replaces.  This
is what turns the abstract replay `recentPages` into the paper's closed form —
the last `k` pages of the initial queue followed by the fetched pages — and
what yields the eviction spacing `i + k < j` between two payments for the same
page.
-/


namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page] {δ : Cost}

/-- Every payment page is absent from the queue obtained from the preceding
payments.  This is the exact history property used by the FIFO suffix proof. -/
inductive FreshPayments (capacity : ℕ) (initial : List Page) : List (Payment Page) → Prop
  | nil : FreshPayments capacity initial []
  | snoc {payments : List (Payment Page)} (h : FreshPayments capacity initial payments)
      (payment : Payment Page)
      (fresh : payment.page ∉ recentPages capacity initial payments) :
      (coherent : payment.queueAfter = recentPages capacity initial (payments ++ [payment])) →
      FreshPayments capacity initial (payments ++ [payment])

theorem FreshPayments.fresh_at {capacity : ℕ} {initial : List Page}
    {payments : List (Payment Page)}
    (h : FreshPayments capacity initial payments) (index : ℕ)
    (hindex : index < payments.length) :
    payments[index].page ∉ recentPages capacity initial (payments.take index) := by
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

theorem FreshPayments.queueAfter_at {capacity : ℕ} {initial : List Page}
    {payments : List (Payment Page)}
    (h : FreshPayments capacity initial payments) (index : ℕ)
    (hindex : index < payments.length) :
    payments[index].queueAfter =
      recentPages capacity initial (payments.take (index + 1)) := by
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
  fresh : FreshPayments input.cacheSize input.initialCache state.payments

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
        exact recentPages_append input.cacheSize input.initialCache state.payments
          state.queue
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
    FreshPayments input.cacheSize input.initialCache
      (run δ input (2 * input.requests.length) (initialState input)).payments := by
  exact (run_freshQueue input valid _ _ (initial_freshQueue input)
    (initial_cacheInvariant input valid)).fresh

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

/-- Concrete FIFO replay is exactly the suffix of length at most `capacity` of
the initial queue followed by the payment pages.  This is the closed form used
by the paper's cache invariant. -/
theorem recentPages_eq_lastPaymentPages (capacity : ℕ) (hpositive : 0 < capacity)
    (initial : List Page) (hinitial : initial.length ≤ capacity)
    (payments : List (Payment Page)) :
    recentPages capacity initial payments = lastPaymentPages capacity initial payments := by
  induction payments using List.reverseRecOn with
  | nil => simp [recentPages, lastPaymentPages, Nat.sub_eq_zero_of_le hinitial]
  | append_singleton payments payment ih =>
      rw [← recentPages_append capacity initial payments
        (recentPages capacity initial payments) payment rfl, ih]
      unfold lastPaymentPages
      simp only [List.map_append, List.map_singleton, ← List.append_assoc]
      exact insertPage_drop_suffix capacity hpositive
        (initial ++ payments.map Payment.page) payment.page

theorem recentPages_take_add (capacity start : ℕ) (hpositive : 0 < capacity)
    (initial : List Page) (hinitial : initial.length ≤ capacity)
    (payments : List (Payment Page)) (hbound : start + capacity ≤ payments.length) :
    recentPages capacity initial (payments.take (start + capacity)) =
      ((payments.drop start).take capacity).map Payment.page := by
  rw [recentPages_eq_lastPaymentPages capacity hpositive initial hinitial]
  unfold lastPaymentPages
  simp only [List.map_take, List.length_take, List.length_map, List.length_append,
    Nat.min_eq_left hbound, List.map_drop]
  rw [show initial.length + (start + capacity) - capacity = initial.length + start by omega,
    List.drop_length_add_append, List.drop_take]
  simp

/-- The closed form read at one index: the entry at position `j` of the initial
queue followed by the payment pages is still in the replayed queue as long as
fewer than `capacity` entries follow it. -/
theorem getElem_mem_recentPages {capacity j : ℕ} (hpositive : 0 < capacity)
    (initial : List Page) (hinitial : initial.length ≤ capacity)
    (payments : List (Payment Page))
    (hj : j < (initial ++ payments.map Payment.page).length)
    (hnear : initial.length + payments.length ≤ j + capacity) :
    (initial ++ payments.map Payment.page)[j] ∈ recentPages capacity initial payments := by
  rw [recentPages_eq_lastPaymentPages capacity hpositive initial hinitial]
  unfold lastPaymentPages
  simp only [List.length_append, List.length_map] at hj ⊢
  let d := initial.length + payments.length - capacity
  have hdle : d ≤ j := by dsimp [d]; omega
  have hidx : j - d < (List.drop d (initial ++ payments.map Payment.page)).length := by
    simp only [List.length_drop, List.length_append, List.length_map]
    omega
  have hm := List.getElem_mem
    (l := List.drop d (initial ++ payments.map Payment.page)) (n := j - d) hidx
  convert hm using 1
  rw [List.getElem_drop]
  congr 1
  omega

/-- A page of the initial queue that no payment has yet evicted is still in
the replayed queue: position `p` of the initial queue is evicted by payment `p`. -/
theorem initial_getElem_mem_recentPages {capacity p : ℕ} (hpositive : 0 < capacity)
    (initial : List Page) (hinitial : initial.length ≤ capacity)
    (payments : List (Payment Page)) (hp : p < initial.length)
    (hlate : payments.length ≤ p) :
    initial[p] ∈ recentPages capacity initial payments := by
  have hj : p < (initial ++ payments.map Payment.page).length := by
    simp only [List.length_append, List.length_map]; omega
  have := getElem_mem_recentPages hpositive initial hinitial payments hj (by omega)
  rwa [List.getElem_append_left hp] at this

theorem page_mem_recentPages_between {capacity i j : ℕ} (hpositive : 0 < capacity)
    (initial : List Page) (hinitial : initial.length ≤ capacity)
    (payments : List (Payment Page)) (hj : j ≤ payments.length)
    (hij : i < j) (hnear : j ≤ i + capacity) :
    payments[i].page ∈ recentPages capacity initial (payments.take j) := by
  rw [recentPages_eq_lastPaymentPages capacity hpositive initial hinitial]
  unfold lastPaymentPages
  simp only [List.map_take, List.length_take, List.length_map, List.length_append,
    Nat.min_eq_left hj]
  let d := initial.length + j - capacity
  have hdle : d ≤ initial.length + i := by dsimp [d]; omega
  have hi : i < payments.length := hij.trans_le hj
  have hidx : initial.length + i - d <
      (List.drop d (initial ++ List.take j (List.map Payment.page payments))).length := by
    simp only [List.length_drop, List.length_append, List.length_take, List.length_map,
      Nat.min_eq_left hj]
    omega
  have hm := List.getElem_mem
    (l := List.drop d (initial ++ List.take j (List.map Payment.page payments)))
    (n := initial.length + i - d) hidx
  convert hm using 1
  rw [List.getElem_drop]
  rw [List.getElem_append_right (by omega)]
  simp [d, hdle]

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
  have hmem : payments[i].page ∈
      recentPages input.cacheSize input.initialCache (payments.take j) :=
    page_mem_recentPages_between valid.positiveCapacity input.initialCache
      valid.initialCache_full.le payments (Nat.le_of_lt hj) hij hnear
  have hfresh := (final_freshPayments input valid).fresh_at j hj
  apply hfresh
  rw [← hpage]
  exact hmem

end PagingWithDelay.FIFO
