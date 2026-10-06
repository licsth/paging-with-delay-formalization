import Proofs.RankPotential.Windows
import Proofs.RankPotential.LazyCache
import Proofs.Analysis.RankPotential
import Proofs.Competitive.DelayAccounting
import Proofs.EventLoop.ServiceBridge

/-!
# Charging the payments

The comparator enters here.  Its events are counted by `eventIndex`: none at
initialization, and `eventIndex (i+1)` events stamped no later than payment
`i`, so that the events between `eventIndex i` and `eventIndex (i+1)` are
those made while FIFO's cache is `queue i`.  The comparator's cache is read
through the lazy cache `L n = lazy n` of `LazyCache.lean`, over the instance's
page universe, and the rank potential is

  `potential i = Φ(queue i, L (eventIndex i))`

at the boundary before payment `i`'s interval.

The write-up's "Potential changes" lemma, in complement form:

* `potential_step_online`: at payment `i`, `Φ' = Φ - m + k·[pageAt i ∈ C_OPT]`
  (`shared_le`, `shared_lt_of_held` bound `m`);
* `gainAt_spec`: at an offline event, `Φ' + k ≥ Φ` — `gainAt` is the
  nonnegative quantity `k + ΔΦ` charged to the event — and
  `gainAt_ge_of_evicted_outside`: it is at least `k` when the evicted page is
  outside FIFO's cache;
* `potential_interval`: the offline changes of one interval telescope.

The three cases of "Payment accounting" for a payment `i`, decided on the lazy
cache `C` just before the payment and over its window:

* `Held i`: `pageAt i ∈ C` — the potential rises by at least one
  (`potential_step_online` with `shared_lt_of_held`);
* `Dropped i`: held at some point of the window but not at its end —
  `dropped_event` finds the last eviction of the page in the window, an
  offline event outside FIFO's cache, of gain `≥ k`; `dropped_event_injective`
  says no event is found twice;
* `Never i`: never held in the window — `threshold_le_delay_of_never` charges
  the delay `δ` of the served requests to the comparator.
-/

namespace PagingWithDelay.RankPotential

open PagingWithDelay Analysis

variable {Page : Type*} [DecidableEq Page]

noncomputable section

variable (S : Setup Page) (comparator : Schedule Page)

/-- The comparator's lazy cache `L n` after its first `n` events, over the
instance's page universe. -/
abbrev lazy (n : ℕ) : Finset Page :=
  Analysis.lazyCache S.cacheSize S.input.pageUniverse comparator n

/-- The number of comparator events up to and including the boundary before
interval `i`: none at initialization, and those stamped no later than payment
`i - 1` afterwards. -/
def eventIndex : ℕ → ℕ
  | 0 => 0
  | i + 1 => Analysis.eventCount comparator (S.timeAt i)

/-- The potential at the boundary before interval `i`. -/
def potential (i : ℕ) : ℕ :=
  rankPotential (S.queue i) (lazy S comparator (eventIndex S comparator i))

/-- The potential immediately before payment `i`, after the offline events of
its interval. -/
def before (i : ℕ) : ℕ :=
  rankPotential (S.queue i) (lazy S comparator (eventIndex S comparator (i + 1)))

/-- `m`: the number of pages shared by both caches immediately before payment `i`. -/
def shared (i : ℕ) : ℕ :=
  (sharedPages (S.queue i) (lazy S comparator (eventIndex S comparator (i + 1)))).card

/-- `k + ΔΦ` at offline event `n`, measured against FIFO's cache `queue i`. -/
def gainAt (i n : ℕ) : ℕ :=
  rankPotential (S.queue i) (lazy S comparator (n + 1)) + S.cacheSize -
    rankPotential (S.queue i) (lazy S comparator n)

/-- The first comparator event of the window of payment `i`: the events after
the last eviction of its page, or all events if it was never evicted. -/
def windowLow (i : ℕ) : ℕ :=
  match S.lastEviction i with
  | none => 0
  | some j => eventIndex S comparator (j + 1)

/-- **Case 1.**  The comparator holds the requested page just before the payment. -/
def Held (i : ℕ) : Prop :=
  S.pageAt i ∈ lazy S comparator (eventIndex S comparator (i + 1))

/-- **Case 2.**  The comparator held the requested page during the window but
no longer does. -/
def Dropped (i : ℕ) : Prop :=
  ¬ Held S comparator i ∧
    ∃ n, windowLow S comparator i ≤ n ∧ n < eventIndex S comparator (i + 1) ∧
      S.pageAt i ∈ lazy S comparator n

/-- **Case 3.**  The comparator never holds the requested page during the window. -/
def Never (i : ℕ) : Prop :=
  ∀ n, windowLow S comparator i ≤ n → n ≤ eventIndex S comparator (i + 1) →
    S.pageAt i ∉ lazy S comparator n

variable {S comparator}

theorem cases_exhaustive (i : ℕ) :
    Held S comparator i ∨ Dropped S comparator i ∨ Never S comparator i := by
  by_cases h1 : Held S comparator i
  · exact Or.inl h1
  refine Or.inr (or_iff_not_imp_left.mpr fun h2 n hlow hhigh hmem => ?_)
  rcases hhigh.lt_or_eq with hlt | rfl
  · exact h2 ⟨h1, n, hlow, hlt, hmem⟩
  · exact h1 hmem

/-- The comparator's initial cache, hence the lazy cache, respects the capacity. -/
theorem initialCache_card_le (feasible : comparator.Feasible S.input) :
    comparator.initialCache.card ≤ S.cacheSize := by
  rw [feasible.initialCache]
  exact (List.toFinset_card_le _).trans S.initialCache_length.le

/-- Within the universe, the lazy cache contains the comparator's cache. -/
theorem mem_lazy_of_mem (feasible : comparator.Feasible S.input) {n : ℕ} {p : Page}
    (hV : p ∈ S.input.pageUniverse) (h : p ∈ Analysis.cacheAfterCount comparator n) :
    p ∈ lazy S comparator n :=
  Analysis.cacheAfterCount_inter_subset_lazyCache (initialCache_card_le feasible)
    feasible.validTransitions feasible.capacity n (Finset.mem_inter.mpr ⟨h, hV⟩)

/-! ### Event indices -/

theorem eventIndex_monotone : Monotone (eventIndex S comparator) := by
  apply monotone_nat_of_le_succ
  intro i
  cases i with
  | zero => exact Nat.zero_le _
  | succ i => exact Analysis.eventCount_mono comparator (S.timeAt_mono (Nat.le_succ i))

theorem eventIndex_le_length (i : ℕ) :
    eventIndex S comparator i ≤ comparator.events.length := by
  cases i with
  | zero => exact Nat.zero_le _
  | succ i => exact Analysis.eventCount_le_length comparator _

/-- The window of payment `i` ends at the boundary after payment `i`. -/
theorem windowLow_le {i : ℕ} (hi : i < S.count) :
    windowLow S comparator i ≤ eventIndex S comparator (i + 1) := by
  unfold windowLow
  cases hl : S.lastEviction i with
  | none => exact Nat.zero_le _
  | some j =>
      exact eventIndex_monotone (Nat.succ_le_succ (S.lastEviction_lt hi hl).le)

/-- Every offline event before boundary `m` lies in one of the intervals before it. -/
theorem exists_interval {n m : ℕ} (hn : n < eventIndex S comparator m) :
    ∃ i < m, eventIndex S comparator i ≤ n ∧ n < eventIndex S comparator (i + 1) := by
  induction m with
  | zero => simp [eventIndex] at hn
  | succ m ih =>
      by_cases hm : n < eventIndex S comparator m
      · obtain ⟨i, hi, h⟩ := ih hm
        exact ⟨i, by omega, h⟩
      · exact ⟨m, m.lt_succ_self, not_lt.mp hm, hn⟩

/-! ### Potential changes at a payment -/

open Classical in
/-- `k·[pageAt i ∈ C_OPT]`. -/
def heldIndicator (S : Setup Page) (comparator : Schedule Page) (i : ℕ) : ℕ :=
  if Held S comparator i then S.cacheSize else 0

/-- **Potential changes, online.**  `Φ' + m = Φ + k·[pageAt i ∈ C_OPT]`. -/
theorem potential_step_online {i : ℕ} (hi : i < S.count) :
    potential S comparator (i + 1) + shared S comparator i =
      before S comparator i + heldIndicator S comparator i := by
  unfold potential before shared heldIndicator Held
  rw [S.queue_succ_full hi, rankPotential_fifo_step (S.queue_nodup hi.le) (S.queue_ne_nil hi.le)
    (S.pageAt_not_mem_queue hi), S.queue_length hi.le]
  congr

theorem shared_le (i : ℕ) (hi : i ≤ S.count) : shared S comparator i ≤ S.cacheSize := by
  unfold shared
  exact (sharedPages_card_le _ _).trans_eq (S.queue_length hi)

theorem shared_lt_of_held (feasible : comparator.Feasible S.input) {i : ℕ} (hi : i < S.count)
    (h : Held S comparator i) : shared S comparator i + 1 ≤ S.cacheSize := by
  have hcard : (lazy S comparator _).card ≤ _ := Analysis.lazyCache_card_le
    (initialCache_card_le feasible) feasible.validTransitions feasible.capacity
    (eventIndex S comparator (i + 1))
  have := sharedPages_card_lt (S.queue i) h (S.pageAt_not_mem_queue hi)
  unfold shared
  omega

/-! ### Potential changes at an offline event -/

/-- **Potential changes, offline.**  The lazy cache evicts at most one page
per event, so `Φ' + k ≥ Φ`: `gainAt` is the nonnegative `k + ΔΦ`. -/
theorem gainAt_spec {i : ℕ} (hi : i ≤ S.count) (n : ℕ) :
    rankPotential (S.queue i) (lazy S comparator (n + 1)) + S.cacheSize =
      rankPotential (S.queue i) (lazy S comparator n) + gainAt S comparator i n := by
  have : rankPotential (S.queue i) (lazy S comparator n) ≤
      rankPotential (S.queue i) (lazy S comparator (n + 1)) + S.cacheSize :=
    S.queue_length hi ▸ rankPotential_le_add_length_of_card_sdiff_le_one _
      (Analysis.card_sdiff_lazyCache_succ_le n)
  unfold gainAt
  omega

/-- An offline event that evicts a page outside FIFO's cache does not lower
the potential: its gain is at least `k`. -/
theorem gainAt_ge_of_evicted_outside {i n : ℕ} (hi : i ≤ S.count) {p : Page}
    (hp : p ∈ lazy S comparator n) (hp' : p ∉ lazy S comparator (n + 1))
    (hnot : p ∉ S.queue i) :
    S.cacheSize ≤ gainAt S comparator i n := by
  have : rankPotential (S.queue i) (lazy S comparator n) ≤
      rankPotential (S.queue i) (lazy S comparator (n + 1)) := by
    simpa [rank, hnot] using rankPotential_le_of_sdiff_subset_singleton (S.queue i)
      (Analysis.sdiff_lazyCache_succ_subset_singleton n hp hp')
  have := gainAt_spec (comparator := comparator) hi n
  omega

/-- The offline changes of an interval telescope: over the events
`a ≤ n < b`, `Φ` rises by the gains and falls by `k` per event. -/
theorem potential_telescope {i : ℕ} (hi : i ≤ S.count) {a b : ℕ} (hab : a ≤ b) :
    rankPotential (S.queue i) (lazy S comparator b) + S.cacheSize * (b - a) =
      rankPotential (S.queue i) (lazy S comparator a) +
        ∑ n ∈ Finset.Ico a b, gainAt S comparator i n := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab, show b + 1 - a = (b - a) + 1 by omega, Nat.mul_succ]
      have := gainAt_spec (comparator := comparator) hi b
      omega

/-- The potential just before payment `i` against the potential at the start
of its interval. -/
theorem potential_interval {i : ℕ} (hi : i ≤ S.count) :
    before S comparator i +
        S.cacheSize * (eventIndex S comparator (i + 1) - eventIndex S comparator i) =
      potential S comparator i +
        ∑ n ∈ Finset.Ico (eventIndex S comparator i) (eventIndex S comparator (i + 1)),
          gainAt S comparator i n :=
  potential_telescope hi (eventIndex_monotone (Nat.le_succ i))

/-! ### Case 2: the associated offline event -/

/-- The last eviction of `pageAt i` in the window of a dropped payment: an
offline event `n` of the window at which the lazy cache loses the page. -/
theorem dropped_event {i : ℕ} (h : Dropped S comparator i) :
    ∃ n, windowLow S comparator i ≤ n ∧ n < eventIndex S comparator (i + 1) ∧
      S.pageAt i ∈ lazy S comparator n ∧ S.pageAt i ∉ lazy S comparator (n + 1) := by
  classical
  obtain ⟨hnot, hex⟩ := h
  -- the last event of the window at which the lazy cache holds the page
  let candidates := (Finset.range (eventIndex S comparator (i + 1))).filter fun n =>
    windowLow S comparator i ≤ n ∧ S.pageAt i ∈ lazy S comparator n
  have hne : candidates.Nonempty := by
    obtain ⟨n, hlow, hhigh, hmem⟩ := hex
    exact ⟨n, by simp [candidates, hlow, hhigh, hmem]⟩
  have hmem := Finset.mem_filter.mp (candidates.max'_mem hne)
  rw [Finset.mem_range] at hmem
  refine ⟨_, hmem.2.1, hmem.1, hmem.2.2, fun hnext => ?_⟩
  rcases (Nat.succ_le_of_lt hmem.1).lt_or_eq with hlt | heq
  · have := candidates.le_max' (candidates.max' hne + 1)
      (by simp [candidates, hlt, hnext, hmem.2.1.trans (Nat.le_succ _)])
    omega
  · exact hnot (by rw [Held, ← heq]; exact hnext)

/-- The interval containing an event of the window of payment `i` is one in
which `pageAt i` is outside FIFO's cache. -/
theorem pageAt_not_mem_queue_of_mem_window {i j n : ℕ} (hi : i < S.count)
    (hlow : windowLow S comparator i ≤ n) (hhigh : n < eventIndex S comparator (i + 1))
    (hj : eventIndex S comparator j ≤ n) (hj' : n < eventIndex S comparator (j + 1)) :
    j ≤ i ∧ S.pageAt i ∉ S.queue j := by
  have hji : j ≤ i := by
    by_contra hcontra
    have := eventIndex_monotone (S := S) (comparator := comparator)
      (show i + 1 ≤ j by omega)
    omega
  refine ⟨hji, S.pageAt_not_mem_queue_of_window hi hji ?_⟩
  intro l hl
  simp only [windowLow, hl] at hlow
  by_contra hcontra
  have := eventIndex_monotone (S := S) (comparator := comparator)
    (show j + 1 ≤ l + 1 by omega)
  omega

/-- **No offline event is associated with two payments.**  The event evicts
one page, so both payments fetch it; their windows are disjoint. -/
theorem dropped_event_injective {i i' n : ℕ} (hi : i < S.count) (hi' : i' < S.count)
    (hlow : windowLow S comparator i ≤ n) (hhigh : n < eventIndex S comparator (i + 1))
    (hmem : S.pageAt i ∈ lazy S comparator n) (hnot : S.pageAt i ∉ lazy S comparator (n + 1))
    (hlow' : windowLow S comparator i' ≤ n) (hhigh' : n < eventIndex S comparator (i' + 1))
    (hmem' : S.pageAt i' ∈ lazy S comparator n) (hnot' : S.pageAt i' ∉ lazy S comparator (n + 1)) :
    i = i' := by
  have hpage : S.pageAt i = S.pageAt i' := Analysis.eq_of_evicted_at n hmem hnot hmem' hnot'
  -- windows of one page are disjoint: the later one starts after the earlier payment
  have key : ∀ a b, a < S.count → b < S.count → a < b → S.pageAt a = S.pageAt b →
      windowLow S comparator b ≤ n → n < eventIndex S comparator (a + 1) → False := by
    intro a b ha hb hab hpage hlowb hhigha
    obtain ⟨j, hj, hjge⟩ := S.lastEviction_ge_of_same_page hb hab hpage
    simp only [windowLow, hj] at hlowb
    have := eventIndex_monotone (S := S) (comparator := comparator)
      (show a + 1 ≤ j + 1 by omega)
    omega
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact key i i' hi hi' hlt hpage hlow' hhigh
  · exact key i' i hi' hi hgt hpage.symm hlow hhigh'

/-! ### Case 3: the delay charge -/

/-- A request served at payment `i` arrives inside the window, in terms of
event indices: the events before its arrival number at least `windowLow i`. -/
theorem windowLow_le_eventCountLT_served {i : ℕ} (hi : i < S.count)
    {occurrence : Occurrence Page} (ho : occurrence ∈ (S.payments[i]).served) :
    windowLow S comparator i ≤ Analysis.eventCountLT comparator occurrence.request.arrival := by
  unfold windowLow
  cases hl : S.lastEviction i with
  | none => exact Nat.zero_le _
  | some j =>
      exact Analysis.eventCount_le_eventCountLT comparator
        (S.served_arrival_gt_lastEviction hi hl ho)

/-- An offline event stamped after the last eviction lies in the window. -/
theorem windowLow_le_of_timeAt_lt (feasible : comparator.Feasible S.input) {i n : ℕ}
    (hn : n < comparator.events.length)
    (htime : ∀ j, S.lastEviction i = some j → S.timeAt j < comparator.events[n].time) :
    windowLow S comparator i ≤ n := by
  unfold windowLow
  cases hl : S.lastEviction i with
  | none => exact Nat.zero_le _
  | some j =>
      by_contra hcontra
      exact (htime j hl).not_ge
        (Analysis.time_le_of_lt_eventCount feasible.chronological hn (Nat.lt_of_not_le hcontra))

/-- **The comparator does not serve a batch it never holds the page for.**
If `pageAt i` is outside the lazy cache throughout the window, the comparator
can serve a request of payment `i` only strictly after `timeAt i`. -/
theorem no_early_service (feasible : comparator.Feasible S.input)
    {i : ℕ} (hi : i < S.count) (hnever : Never S comparator i)
    {occurrence : Occurrence Page} (ho : occurrence ∈ (S.payments[i]).served)
    {time : Time} (hmem : time ∈ comparator.serviceCandidates occurrence.request) :
    S.timeAt i < time := by
  have hpage : occurrence.request.page = S.pageAt i := S.served_page hi ho
  have hV := S.pageAt_mem_pageUniverse hi
  -- the comparator does not hold the page when the request arrives
  have hnothit : occurrence.request.page ∉
      comparator.cacheBefore occurrence.request.arrival := by
    rw [Analysis.cacheBefore_eq_cacheAfterCount feasible.chronological, hpage]
    exact fun h => hnever _ (windowLow_le_eventCountLT_served hi ho)
      (Analysis.eventCountLT_le_eventCount comparator (S.served_arrival_le hi ho))
      (mem_lazy_of_mem feasible hV h)
  -- hence the only service candidates are fetches of the page
  rw [Schedule.serviceCandidates, if_neg hnothit, List.mem_toFinset, List.mem_map] at hmem
  obtain ⟨event, hevent, rfl⟩ := hmem
  obtain ⟨hmemEvent, harrival, hfetched⟩ : event ∈ comparator.events ∧
      occurrence.request.arrival ≤ event.time ∧ occurrence.request.page = event.fetched := by
    simpa using hevent
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hmemEvent
  by_contra hlt
  have hupper : n < eventIndex S comparator (i + 1) :=
    Analysis.lt_eventCount_of_time_le feasible.chronological hn (not_lt.mp hlt)
  have hlower : windowLow S comparator i ≤ n := windowLow_le_of_timeAt_lt feasible hn
    fun j hj => (S.served_arrival_gt_lastEviction hi hj ho).trans_le harrival
  refine hnever (n + 1) (by omega) (by omega) (mem_lazy_of_mem feasible hV ?_)
  rw [← hpage, hfetched]
  exact Analysis.fetched_mem_cacheAfterCount comparator feasible.validTransitions hn

/-- In Case 3, the comparator's delay for a request of payment `i` is its delay
up to some time strictly after `timeAt i`. -/
theorem exists_requestCost_eq_of_never (feasible : comparator.Feasible S.input)
    {i : ℕ} (hi : i < S.count) (hnever : Never S comparator i)
    {occurrence : Occurrence Page} (ho : occurrence ∈ (S.payments[i]).served) :
    ∃ time, S.timeAt i < time ∧ comparator.requestCost occurrence.request =
      occurrence.request.delay (time - occurrence.request.arrival) := by
  have hserved := feasible.eventuallyServed _ (S.served_request_mem hi ho)
  exact ⟨_, no_early_service feasible hi hnever ho (Finset.min'_mem _ hserved),
    Schedule.requestCost_eq_of_serviceTime _ _ _ (by simp [Schedule.serviceTime, hserved])⟩

/-- **Case 3 charges the threshold.**  The requests served at a never-held
payment cost the comparator at least `δ` of delay altogether. -/
theorem threshold_le_delay_of_never (feasible : comparator.Feasible S.input)
    {i : ℕ} (hi : i < S.count) (hnever : Never S comparator i) :
    S.threshold ≤
      ((S.payments[i]).served.map fun occurrence =>
        comparator.requestCost occurrence.request).sum := by
  rw [← S.payment_delayCost hi, FIFO.Payment.delayCost, ← S.timeAt_eq hi]
  refine List.sum_le_sum fun occurrence ho => ?_
  obtain ⟨time, htime, heq⟩ := exists_requestCost_eq_of_never feasible hi hnever ho
  exact heq ▸ occurrence.request.delay_mono (tsub_le_tsub_right htime.le _)

omit [DecidableEq Page] in
private theorem exists_lt_le_all {α : Type*} (l : List α) (g : α → Time) {T : Time}
    (h : ∀ x ∈ l, T < g x) : ∃ t, T < t ∧ ∀ x ∈ l, t ≤ g x := by
  induction l with
  | nil => exact ⟨T + 1, lt_add_one T, by simp⟩
  | cons a l ih =>
      obtain ⟨t, ht, hall⟩ := ih fun x hx => h x (List.mem_cons_of_mem a hx)
      refine ⟨min t (g a), lt_min ht (h a List.mem_cons_self), ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hall x hx)

/-- **Case 3 costs the comparator delay**, for deadline-triggered FIFO: the
comparator serves the requests of a never-held payment strictly after it, when
one of them is past its deadline.  So a comparator meeting every deadline
has no never-held payment. -/
theorem delay_pos_of_never (hdeadline : S.trigger = .deadline)
    (feasible : comparator.Feasible S.input) {i : ℕ} (hi : i < S.count) (hnever : Never S comparator i) :
    0 < ((S.payments[i]).served.map fun occurrence =>
      comparator.requestCost occurrence.request).sum := by
  choose! time htime heq using fun occurrence (ho : occurrence ∈ (S.payments[i]).served) =>
    exists_requestCost_eq_of_never feasible hi hnever ho
  obtain ⟨t, ht, hle⟩ := exists_lt_le_all _ time htime
  refine (S.payment_due hdeadline hi ht).trans_le (List.sum_le_sum fun occurrence ho => ?_)
  rw [heq occurrence ho]
  exact occurrence.request.delay_mono (tsub_le_tsub_right (hle occurrence ho) _)

end

end PagingWithDelay.RankPotential
