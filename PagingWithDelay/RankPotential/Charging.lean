import PagingWithDelay.RankPotential.Windows
import PagingWithDelay.RankPotential.LazyCache
import PagingWithDelay.Analysis.RankPotential
import PagingWithDelay.Competitive.DelayAccounting
import PagingWithDelay.EventLoop.ServiceBridge

/-!
# Charging the payments

The comparator enters here.  Its events are counted by `eventIndex`: none at
initialization, and `eventIndex (i+1)` events stamped no later than payment
`i`, so that the events between `eventIndex i` and `eventIndex (i+1)` are
those made while FIFO's cache is `queue i`.  The comparator's cache is read
through the lazy cache `L n` of `LazyCache.lean`, and the rank potential is

  `potential i = Φ(queue i, L (eventIndex i))`

at the boundary before payment `i`'s interval.

The write-up's "Potential changes" lemma:

* `potential_step_online`: at payment `i`, `Φ' = Φ - m + k·[pageAt i ∈ C_OPT]`
  (`shared_le`, `shared_lt_of_held` bound `m`);
* `gainAt_spec`: at an offline event, `Φ' + k ≥ Φ` — `gainAt` is the
  nonnegative quantity `k + ΔΦ` charged to the event — and
  `gainAt_ge_of_evicted_outside`: it is at least `k` when the evicted page is
  outside FIFO's cache;
* `potential_interval`: the offline changes of one interval telescope.

The three cases of "Payment accounting" for a payment `i`, decided on the lazy
cache `C` just before the payment and over its window:

* `Held i`: `pageAt i ∈ C` — the potential rises by one (`potential_step_online`
  with `shared_lt_of_held`);
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

/-- The number of comparator events up to and including the boundary before
interval `i`: none at initialization, and those stamped no later than payment
`i - 1` afterwards. -/
def eventIndex : ℕ → ℕ
  | 0 => 0
  | i + 1 => Analysis.eventCount comparator (S.timeAt i)

/-- The potential at the boundary before interval `i`. -/
def potential (i : ℕ) : ℕ := rankPotential (S.queue i) (Analysis.lazyCache S.cacheSize comparator (eventIndex S comparator i))

/-- The potential immediately before payment `i`, after the offline events of
its interval. -/
def before (i : ℕ) : ℕ :=
  rankPotential (S.queue i) (Analysis.lazyCache S.cacheSize comparator (eventIndex S comparator (i + 1)))

/-- `m`: the number of pages shared by both caches immediately before payment `i`. -/
def shared (i : ℕ) : ℕ :=
  (sharedPages (S.queue i) (Analysis.lazyCache S.cacheSize comparator (eventIndex S comparator (i + 1)))).card

/-- `k + ΔΦ` at offline event `n`, measured against FIFO's cache `queue i`. -/
def gainAt (i n : ℕ) : ℕ :=
  rankPotential (S.queue i) (Analysis.lazyCache S.cacheSize comparator (n + 1)) + S.cacheSize -
    rankPotential (S.queue i) (Analysis.lazyCache S.cacheSize comparator n)

/-- The first comparator event of the window of payment `i`: the events after
the last eviction of its page, or all events if it was never evicted. -/
def windowLow (i : ℕ) : ℕ :=
  match S.lastEviction i with
  | none => 0
  | some j => eventIndex S comparator (j + 1)

/-- **Case 1.**  The comparator holds the requested page just before the payment. -/
def Held (i : ℕ) : Prop := S.pageAt i ∈ Analysis.lazyCache S.cacheSize comparator (eventIndex S comparator (i + 1))

/-- **Case 2.**  The comparator held the requested page during the window but
no longer does. -/
def Dropped (i : ℕ) : Prop :=
  ¬ Held S comparator i ∧
    ∃ n, windowLow S comparator i ≤ n ∧ n < eventIndex S comparator (i + 1) ∧
      S.pageAt i ∈ Analysis.lazyCache S.cacheSize comparator n

/-- **Case 3.**  The comparator never holds the requested page during the window. -/
def Never (i : ℕ) : Prop :=
  ∀ n, windowLow S comparator i ≤ n → n ≤ eventIndex S comparator (i + 1) →
    S.pageAt i ∉ Analysis.lazyCache S.cacheSize comparator n

variable {S comparator}

theorem cases_exhaustive (i : ℕ) :
    Held S comparator i ∨ Dropped S comparator i ∨ Never S comparator i := by
  by_cases h1 : Held S comparator i
  · exact Or.inl h1
  by_cases h2 : ∃ n, windowLow S comparator i ≤ n ∧ n < eventIndex S comparator (i + 1) ∧
      S.pageAt i ∈ Analysis.lazyCache S.cacheSize comparator n
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · refine Or.inr (Or.inr ?_)
    intro n hlow hhigh hmem
    rcases Nat.lt_or_ge n (eventIndex S comparator (i + 1)) with hlt | hge
    · exact h2 ⟨n, hlow, hlt, hmem⟩
    · have : n = eventIndex S comparator (i + 1) := by omega
      exact h1 (by unfold Held; rw [← this]; exact hmem)

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

theorem eventIndex_succ_le_of_timeAt_lt {j i : ℕ} (h : S.timeAt j < S.timeAt i) :
    eventIndex S comparator (j + 1) ≤ eventIndex S comparator (i + 1) :=
  Analysis.eventCount_mono comparator h.le

/-- The window of payment `i` ends at the boundary after payment `i`. -/
theorem windowLow_le {i : ℕ} (hi : i < S.count) :
    windowLow S comparator i ≤ eventIndex S comparator (i + 1) := by
  unfold windowLow
  cases hl : S.lastEviction i with
  | none => exact Nat.zero_le _
  | some j =>
      exact eventIndex_monotone (Nat.succ_le_succ (S.lastEviction_lt hi hl).le)

/-- Every offline event before the last boundary lies in exactly one interval. -/
theorem exists_interval {n : ℕ} (hn : n < eventIndex S comparator S.count) :
    ∃ i < S.count, eventIndex S comparator i ≤ n ∧ n < eventIndex S comparator (i + 1) := by
  have key : ∀ m, n < eventIndex S comparator m →
      ∃ i < m, eventIndex S comparator i ≤ n ∧ n < eventIndex S comparator (i + 1) := by
    intro m
    induction m with
    | zero => intro h; simp [eventIndex] at h
    | succ m ih =>
        intro h
        by_cases hm : n < eventIndex S comparator m
        · obtain ⟨i, hi, hlow, hhigh⟩ := ih hm
          exact ⟨i, by omega, hlow, hhigh⟩
        · exact ⟨m, Nat.lt_succ_self m, Nat.le_of_not_lt hm, h⟩
  exact key S.count hn

/-! ### Potential changes at a payment -/

/-- **Potential changes, online.**  `Φ' + m = Φ + k·[pageAt i ∈ C_OPT]`: the
case where the comparator holds the page. -/
theorem potential_step_online_of_held {i : ℕ} (hi : i < S.count) (h : Held S comparator i) :
    potential S comparator (i + 1) + shared S comparator i =
      before S comparator i + S.cacheSize := by
  unfold potential before shared
  rw [S.queue_succ_full hi]
  have := rankPotential_fifo_step (S.queue_nodup hi.le) (S.queue_ne_nil hi.le)
    (S.pageAt_not_mem_queue hi)
    (Analysis.lazyCache S.cacheSize comparator (eventIndex S comparator (i + 1)))
  rw [this, S.queue_length hi.le, if_pos (show S.pageAt i ∈ _ from h)]

/-- **Potential changes, online.**  `Φ' + m = Φ + k·[pageAt i ∈ C_OPT]`: the
case where the comparator does not hold the page. -/
theorem potential_step_online_of_not_held {i : ℕ} (hi : i < S.count)
    (h : ¬ Held S comparator i) :
    potential S comparator (i + 1) + shared S comparator i = before S comparator i := by
  unfold potential before shared
  rw [S.queue_succ_full hi]
  have := rankPotential_fifo_step (S.queue_nodup hi.le) (S.queue_ne_nil hi.le)
    (S.pageAt_not_mem_queue hi)
    (Analysis.lazyCache S.cacheSize comparator (eventIndex S comparator (i + 1)))
  rw [this, if_neg (show S.pageAt i ∉ _ from h), add_zero]

theorem shared_le (i : ℕ) (hi : i ≤ S.count) : shared S comparator i ≤ S.cacheSize := by
  unfold shared
  exact (sharedPages_card_le _ _).trans_eq (S.queue_length hi)

theorem shared_lt_of_held (feasible : comparator.Feasible S.input) {i : ℕ} (hi : i < S.count)
    (h : Held S comparator i) : shared S comparator i + 1 ≤ S.cacheSize := by
  unfold shared
  have hcard := Analysis.lazyCache_card_le (k := S.cacheSize) (schedule := comparator)
    (by rw [feasible.initialCache, ← S.size]
        exact (List.toFinset_card_le _).trans S.valid.initialCache_full.le)
    feasible.validTransitions (fun e he => S.size ▸ feasible.capacity e he)
    (eventIndex S comparator (i + 1))
  have := sharedPages_card_lt (S.queue i) h (S.pageAt_not_mem_queue hi)
  omega

/-! ### Potential changes at an offline event -/

/-- **Potential changes, offline.**  The lazy cache evicts at most one page
per event, so `Φ' + k ≥ Φ`: `gainAt` is the nonnegative `k + ΔΦ`. -/
theorem gainAt_spec {i : ℕ} (hi : i ≤ S.count) (n : ℕ) :
    rankPotential (S.queue i) (Analysis.lazyCache S.cacheSize comparator (n + 1)) + S.cacheSize =
      rankPotential (S.queue i) (Analysis.lazyCache S.cacheSize comparator n) + gainAt S comparator i n := by
  unfold gainAt
  have := rankPotential_le_add_length_of_card_sdiff_le_one (S.queue i)
    (Analysis.card_sdiff_lazyCache_succ_le (k := S.cacheSize) (schedule := comparator) n)
  rw [S.queue_length hi] at this
  omega

/-- An offline event that evicts a page outside FIFO's cache does not lower
the potential: its gain is at least `k`. -/
theorem gainAt_ge_of_evicted_outside {i n : ℕ} (hi : i ≤ S.count) {p : Page}
    (hp : p ∈ Analysis.lazyCache S.cacheSize comparator n) (hp' : p ∉ Analysis.lazyCache S.cacheSize comparator (n + 1)) (hnot : p ∉ S.queue i) :
    S.cacheSize ≤ gainAt S comparator i n := by
  unfold gainAt
  have := rankPotential_le_of_sdiff_subset_singleton (S.queue i)
    (Analysis.sdiff_lazyCache_succ_subset_singleton (k := S.cacheSize) (schedule := comparator)
      n hp hp')
  have hrank : rank (S.queue i) p = 0 := by simp [rank, hnot]
  rw [hrank, add_zero] at this
  have hspec := gainAt_spec (comparator := comparator) hi n
  unfold gainAt at hspec
  omega

/-- The offline changes of an interval telescope: over the events
`a ≤ n < b`, `Φ` rises by the gains and falls by `k` per event. -/
theorem potential_telescope {i : ℕ} (hi : i ≤ S.count) {a b : ℕ} (hab : a ≤ b) :
    rankPotential (S.queue i) (Analysis.lazyCache S.cacheSize comparator b) + S.cacheSize * (b - a) =
      rankPotential (S.queue i) (Analysis.lazyCache S.cacheSize comparator a) +
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
      S.pageAt i ∈ Analysis.lazyCache S.cacheSize comparator n ∧ S.pageAt i ∉ Analysis.lazyCache S.cacheSize comparator (n + 1) := by
  obtain ⟨hnot, hex⟩ := h
  classical
  set candidates := (Finset.range (eventIndex S comparator (i + 1))).filter fun n =>
    windowLow S comparator i ≤ n ∧ S.pageAt i ∈ Analysis.lazyCache S.cacheSize comparator n with hc
  have hne : candidates.Nonempty := by
    obtain ⟨n, hlow, hhigh, hmem⟩ := hex
    exact ⟨n, by simp [hc, hlow, hhigh, hmem]⟩
  set n := candidates.max' hne with hn
  have hmem : n ∈ candidates := Finset.max'_mem _ hne
  simp only [hc, Finset.mem_filter, Finset.mem_range] at hmem
  refine ⟨n, hmem.2.1, hmem.1, hmem.2.2, ?_⟩
  intro hnext
  rcases Nat.lt_or_ge (n + 1) (eventIndex S comparator (i + 1)) with hlt | hge
  · have : n + 1 ∈ candidates := by simp [hc, hlt, hnext, hmem.2.1.trans (Nat.le_succ n)]
    have := Finset.le_max' _ _ this
    omega
  · have : n + 1 = eventIndex S comparator (i + 1) := by omega
    exact hnot (by unfold Held; rw [← this]; exact hnext)

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
    (hmem : S.pageAt i ∈ Analysis.lazyCache S.cacheSize comparator n) (hnot : S.pageAt i ∉ Analysis.lazyCache S.cacheSize comparator (n + 1))
    (hlow' : windowLow S comparator i' ≤ n) (hhigh' : n < eventIndex S comparator (i' + 1))
    (hmem' : S.pageAt i' ∈ Analysis.lazyCache S.cacheSize comparator n) (hnot' : S.pageAt i' ∉ Analysis.lazyCache S.cacheSize comparator (n + 1)) :
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

/-- Lazy-cache membership implies real-cache membership, contrapositively. -/
theorem notMem_cacheAfterCount_of_notMem_L (feasible : comparator.Feasible S.input)
    {n : ℕ} {p : Page} (h : p ∉ Analysis.lazyCache S.cacheSize comparator n) : p ∉ Analysis.cacheAfterCount comparator n :=
  fun hmem => h (Analysis.cacheAfterCount_subset_lazyCache (k := S.cacheSize)
    (by rw [feasible.initialCache, ← S.size]
        exact (List.toFinset_card_le _).trans S.valid.initialCache_full.le)
    feasible.validTransitions (fun e he => S.size ▸ feasible.capacity e he) n hmem)

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
      have := Analysis.time_le_of_lt_eventCount feasible.chronological hn (Nat.lt_of_not_le hcontra)
      exact absurd (htime j hl) (not_lt.mpr this)

/-- **The comparator does not serve a batch it never holds the page for.**
If `pageAt i` is outside the lazy cache throughout the window, every request
served at payment `i` is served by the comparator no earlier than `timeAt i`. -/
theorem no_early_service (feasible : comparator.Feasible S.input)
    {i : ℕ} (hi : i < S.count) (hnever : Never S comparator i)
    {occurrence : Occurrence Page} (ho : occurrence ∈ (S.payments[i]).served)
    {time : Time} (hmem : time ∈ comparator.serviceTime occurrence.request) :
    S.timeAt i ≤ time := by
  have hpage : occurrence.request.page = S.pageAt i := S.served_page hi ho
  have hbefore : occurrence.request.arrival ≤ S.timeAt i := S.served_arrival_le hi ho
  -- the comparator does not hold the page when the request arrives
  have hnothit : occurrence.request.page ∉
      comparator.cacheBefore occurrence.request.arrival := by
    rw [Analysis.cacheBefore_eq_cacheAfterCount feasible.chronological, hpage]
    apply notMem_cacheAfterCount_of_notMem_L feasible
    exact hnever _ (windowLow_le_eventCountLT_served hi ho)
      (Analysis.eventCountLT_le_eventCount comparator hbefore)
  -- hence the only service candidates are fetches of the page
  have hcandidate : time ∈ comparator.serviceCandidates occurrence.request := by
    rw [Option.mem_def, Schedule.serviceTime] at hmem
    split at hmem
    · rename_i hnonempty
      have heq : (comparator.serviceCandidates occurrence.request).min' hnonempty = time :=
        Option.some_inj.mp hmem
      rw [← heq]
      exact Finset.min'_mem _ hnonempty
    · exact absurd hmem.symm (Option.some_ne_none time)
  rw [Schedule.serviceCandidates, if_neg hnothit, List.mem_toFinset, List.mem_map] at hcandidate
  obtain ⟨event, hevent, htime⟩ := hcandidate
  rw [List.mem_filter] at hevent
  obtain ⟨hmemEvent, hcond⟩ := hevent
  simp only [decide_eq_true_eq] at hcond
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn, hgetElem⟩ := List.mem_iff_getElem.mp hmemEvent
  have hntime : comparator.events[n].time = time := by rw [hgetElem]; exact htime
  have hupper : n < eventIndex S comparator (i + 1) := by
    refine Analysis.lt_eventCount_of_time_le feasible.chronological hn ?_
    rw [hntime]
    exact le_of_lt hlt
  have hlower : windowLow S comparator i ≤ n := by
    refine windowLow_le_of_timeAt_lt feasible hn ?_
    intro j hj
    rw [hntime]
    exact (S.served_arrival_gt_lastEviction hi hj ho).trans_le (htime ▸ hcond.1)
  apply hnever (n + 1) (by omega) (by omega)
  apply Analysis.cacheAfterCount_subset_lazyCache (k := S.cacheSize)
    (by rw [feasible.initialCache, ← S.size]
        exact (List.toFinset_card_le _).trans S.valid.initialCache_full.le)
    feasible.validTransitions (fun e he => S.size ▸ feasible.capacity e he)
  rw [← hpage, hcond.2, ← hgetElem]
  exact Analysis.fetched_mem_cacheAfterCount comparator feasible.validTransitions hn

/-- **Case 3 charges the threshold.**  The requests served at a never-held
payment cost the comparator at least `δ` of delay altogether. -/
theorem threshold_le_delay_of_never (feasible : comparator.Feasible S.input)
    {i : ℕ} (hi : i < S.count) (hnever : Never S comparator i) :
    S.threshold ≤
      ((S.payments[i]).served.map fun occurrence =>
        comparator.requestCost occurrence.request).sum := by
  have hterm : ∀ occurrence ∈ (S.payments[i]).served,
      occurrence.request.delay (S.timeAt i - occurrence.request.arrival) ≤
        comparator.requestCost occurrence.request := by
    intro occurrence ho
    have hserved := feasible.eventuallyServed occurrence.request (S.served_request_mem hi ho)
    have hservice : comparator.serviceTime occurrence.request =
        some ((comparator.serviceCandidates occurrence.request).min' hserved) := by
      simp [Schedule.serviceTime, hserved]
    rw [Schedule.requestCost_eq_of_serviceTime _ _ _ hservice]
    apply occurrence.request.delay_mono
    apply tsub_le_tsub_right
    exact no_early_service feasible hi hnever ho (by rw [hservice]; rfl)
  calc S.threshold = (S.payments[i]).delayCost := (S.payment_delayCost hi).symm
    _ = ((S.payments[i]).served.map fun occurrence =>
          occurrence.request.delay (S.timeAt i - occurrence.request.arrival)).sum := by
        rw [FIFO.Payment.delayCost, S.timeAt_eq hi]
    _ ≤ _ := List.sum_le_sum hterm

end

end PagingWithDelay.RankPotential
