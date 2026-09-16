import PagingWithDelay.Analysis.CacheTrace

/-!
# The lazy offline cache

The write-up assumes that `OPT` "evicts a page only when fetching another page
into a full cache".  `Schedule.Feasible` is more permissive: one fetch event
may evict any number of pages, and may fetch pages outside the instance's
universe.  Instead of restricting the model, the competitive analysis reads
the comparator through a *lazy cache*: a sequence `lazyCache k V comparator n`
of sets, one per comparator event, which

* starts at the comparator's initial cache (`lazyCache_zero`);
* contains, at every step, the part of the comparator's actual cache inside
  the page universe `V` (`cacheAfterCount_inter_subset_lazyCache`);
* never exceeds the cache capacity (`lazyCache_card_le`);
* changes at event `n` only by adding the fetched page, when it lies in `V`,
  and removing at most one page (`lazyCache_succ_sdiff_subset`,
  `card_sdiff_lazyCache_succ_le`, `exists_fetched_of_evicted`).

The lazy cache keeps every page until its slot is needed; when the fetched
page is already present, or outside the universe, nothing happens.  It is an
analysis device only — no schedule is built from it — so the comparator's
fetch count and delay cost in the competitive statement are those of the
comparator itself.
-/

namespace PagingWithDelay.Analysis

open Finset

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- One lazy step: on a fetch of a page already held or outside the universe,
nothing; otherwise add the page, first evicting one page the comparator does
not hold afterwards if the lazy cache is full.  The last branch is unreachable
under the capacity bounds. -/
def lazyStep (k : ℕ) (V : Finset Page) (lazy : Finset Page) (event : FetchEvent Page) :
    Finset Page :=
  if event.fetched ∉ V ∨ event.fetched ∈ lazy then lazy
  else if lazy.card < k then insert event.fetched lazy
  else if h : (lazy \ event.cacheAfter).Nonempty then insert event.fetched (lazy.erase h.choose)
  else insert event.fetched lazy

/-- The lazy cache after the first `n` comparator events. -/
def lazyCache (k : ℕ) (V : Finset Page) (schedule : Schedule Page) : ℕ → Finset Page
  | 0 => schedule.initialCache
  | n + 1 =>
      match schedule.events[n]? with
      | none => lazyCache k V schedule n
      | some event => lazyStep k V (lazyCache k V schedule n) event

variable (k : ℕ) (V : Finset Page) (schedule : Schedule Page)

@[simp] theorem lazyCache_zero : lazyCache k V schedule 0 = schedule.initialCache := rfl

theorem lazyCache_succ_of_lt {n : ℕ} (hn : n < schedule.events.length) :
    lazyCache k V schedule (n + 1) =
      lazyStep k V (lazyCache k V schedule n) schedule.events[n] := by
  simp [lazyCache, List.getElem?_eq_getElem hn]

theorem lazyCache_succ_of_le {n : ℕ} (hn : schedule.events.length ≤ n) :
    lazyCache k V schedule (n + 1) = lazyCache k V schedule n := by
  simp [lazyCache, List.getElem?_eq_none_iff.mpr hn]

/-! ### One step -/

theorem lazyStep_sdiff_subset (lazy : Finset Page) (event : FetchEvent Page) :
    lazyStep k V lazy event \ lazy ⊆ {event.fetched} := by
  unfold lazyStep
  split_ifs <;> intro q hq <;> simp only [Finset.mem_sdiff, Finset.mem_insert,
    Finset.mem_erase, Finset.mem_singleton] at hq ⊢ <;> tauto

/-- A step that evicts a page has inserted the fetched page, a page of the
universe that was absent before. -/
theorem exists_fetched_of_lazyStep_evicts (lazy : Finset Page) (event : FetchEvent Page)
    {p : Page} (hp : p ∈ lazy) (hp' : p ∉ lazyStep k V lazy event) :
    event.fetched ∈ V ∧ event.fetched ∉ lazy ∧ event.fetched ∈ lazyStep k V lazy event := by
  unfold lazyStep at hp' ⊢
  split_ifs at hp' ⊢ with h1 h2 h3
  · exact absurd hp hp'
  · push_neg at h1
    exact ⟨h1.1, h1.2, Finset.mem_insert_self _ _⟩
  · push_neg at h1
    exact ⟨h1.1, h1.2, Finset.mem_insert_self _ _⟩
  · push_neg at h1
    exact ⟨h1.1, h1.2, Finset.mem_insert_self _ _⟩

theorem card_sdiff_lazyStep_le (lazy : Finset Page) (event : FetchEvent Page) :
    (lazy \ lazyStep k V lazy event).card ≤ 1 := by
  unfold lazyStep
  split_ifs with h1 h2 h3
  · simp
  · rw [Finset.card_eq_zero.mpr]
    · exact Nat.zero_le _
    · rw [Finset.sdiff_eq_empty_iff_subset]
      exact Finset.subset_insert _ _
  · refine (Finset.card_le_card ?_).trans (Finset.card_singleton h3.choose).le
    intro q hq
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or, not_and,
      Finset.mem_singleton] at hq ⊢
    by_contra hne
    exact hq.2.2 hne hq.1
  · rw [Finset.card_eq_zero.mpr]
    · exact Nat.zero_le _
    · rw [Finset.sdiff_eq_empty_iff_subset]
      exact Finset.subset_insert _ _

/-- The invariant step: if the lazy cache contains the previous actual cache
within the universe and both respect the capacity, the same holds after the
event. -/
theorem lazyStep_spec {lazy previous : Finset Page} (hsub : previous ∩ V ⊆ lazy)
    (hlazy : lazy.card ≤ k) {event : FetchEvent Page}
    (hvalid : event.cacheAfter \ previous = {event.fetched})
    (hcap : event.cacheAfter.card ≤ k) :
    event.cacheAfter ∩ V ⊆ lazyStep k V lazy event ∧ (lazyStep k V lazy event).card ≤ k := by
  have hafter : ∀ q ∈ event.cacheAfter, q = event.fetched ∨ q ∈ previous := by
    intro q hq
    by_cases hp : q ∈ previous
    · exact Or.inr hp
    · have : q ∈ event.cacheAfter \ previous := Finset.mem_sdiff.mpr ⟨hq, hp⟩
      rw [hvalid, Finset.mem_singleton] at this
      exact Or.inl this
  have hfetched : event.fetched ∈ event.cacheAfter := by
    have : event.fetched ∈ event.cacheAfter \ previous := by rw [hvalid]; simp
    exact (Finset.mem_sdiff.mp this).1
  unfold lazyStep
  split_ifs with h1 h2 h3
  · refine ⟨?_, hlazy⟩
    intro q hq
    rw [Finset.mem_inter] at hq
    rcases hafter q hq.1 with rfl | hp
    · rcases h1 with h1 | h1
      · exact absurd hq.2 h1
      · exact h1
    · exact hsub (Finset.mem_inter.mpr ⟨hp, hq.2⟩)
  · push_neg at h1
    refine ⟨?_, ?_⟩
    · intro q hq
      rw [Finset.mem_inter] at hq
      rcases hafter q hq.1 with rfl | hp
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hsub (Finset.mem_inter.mpr ⟨hp, hq.2⟩))
    · rw [Finset.card_insert_of_notMem h1.2]
      exact h2
  · push_neg at h1
    refine ⟨?_, ?_⟩
    · intro q hq
      rw [Finset.mem_inter] at hq
      rcases hafter q hq.1 with rfl | hp
      · exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        rw [Finset.mem_erase]
        refine ⟨?_, hsub (Finset.mem_inter.mpr ⟨hp, hq.2⟩)⟩
        intro heq
        have := h3.choose_spec
        rw [← heq] at this
        exact (Finset.mem_sdiff.mp this).2 hq.1
    · rw [Finset.card_insert_of_notMem (fun h => h1.2 (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem (Finset.mem_sdiff.mp h3.choose_spec).1]
      have := Finset.card_pos.mpr ⟨_, (Finset.mem_sdiff.mp h3.choose_spec).1⟩
      omega
  · -- unreachable: the lazy cache is full and inside the new cache, which lacks room
    exfalso
    push_neg at h1
    have hsub' : lazy ⊆ event.cacheAfter.erase event.fetched := by
      intro q hq
      rw [Finset.mem_erase]
      refine ⟨fun heq => h1.2 (by rw [← heq]; exact hq), ?_⟩
      by_contra hnot
      exact h3 ⟨q, Finset.mem_sdiff.mpr ⟨hq, hnot⟩⟩
    have hpos := Finset.card_pos.mpr ⟨_, hfetched⟩
    have := Finset.card_le_card hsub'
    rw [Finset.card_erase_of_mem hfetched] at this
    omega

/-! ### The invariant along the trace -/

variable {k V schedule}

theorem cacheAfterCount_inter_subset_lazyCache_and_card_le
    (hinit : schedule.initialCache.card ≤ k)
    (htransitions : Schedule.ValidTransitionsFrom schedule.initialCache schedule.events)
    (hcap : ∀ event ∈ schedule.events, event.cacheAfter.card ≤ k) (n : ℕ) :
    cacheAfterCount schedule n ∩ V ⊆ lazyCache k V schedule n ∧
      (lazyCache k V schedule n).card ≤ k := by
  induction n with
  | zero => exact ⟨Finset.inter_subset_left, hinit⟩
  | succ n ih =>
      by_cases hn : n < schedule.events.length
      · rw [lazyCache_succ_of_lt k V schedule hn, cacheAfterCount_succ schedule hn]
        have hstep := validTransitions_getElem htransitions n hn
        exact lazyStep_spec k V ih.1 ih.2
          (by simpa [cacheAfterCount] using hstep.2) (hcap _ (List.getElem_mem hn))
      · rw [lazyCache_succ_of_le k V schedule (Nat.le_of_not_lt hn)]
        have : cacheAfterCount schedule (n + 1) = cacheAfterCount schedule n := by
          unfold cacheAfterCount
          rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        rw [this]
        exact ih

/-- Within the universe, the lazy cache contains the actual cache. -/
theorem cacheAfterCount_inter_subset_lazyCache
    (hinit : schedule.initialCache.card ≤ k)
    (htransitions : Schedule.ValidTransitionsFrom schedule.initialCache schedule.events)
    (hcap : ∀ event ∈ schedule.events, event.cacheAfter.card ≤ k) (n : ℕ) :
    cacheAfterCount schedule n ∩ V ⊆ lazyCache k V schedule n :=
  (cacheAfterCount_inter_subset_lazyCache_and_card_le hinit htransitions hcap n).1

theorem lazyCache_card_le
    (hinit : schedule.initialCache.card ≤ k)
    (htransitions : Schedule.ValidTransitionsFrom schedule.initialCache schedule.events)
    (hcap : ∀ event ∈ schedule.events, event.cacheAfter.card ≤ k) (n : ℕ) :
    (lazyCache k V schedule n).card ≤ k :=
  (cacheAfterCount_inter_subset_lazyCache_and_card_le hinit htransitions hcap n).2

/-- Event `n < length` adds at most the page it fetches. -/
theorem lazyCache_succ_sdiff_subset {n : ℕ} (hn : n < schedule.events.length) :
    lazyCache k V schedule (n + 1) \ lazyCache k V schedule n ⊆
      {schedule.events[n].fetched} := by
  rw [lazyCache_succ_of_lt k V schedule hn]
  exact lazyStep_sdiff_subset k V _ _

/-- Event `n` evicts at most one page. -/
theorem card_sdiff_lazyCache_succ_le (n : ℕ) :
    (lazyCache k V schedule n \ lazyCache k V schedule (n + 1)).card ≤ 1 := by
  by_cases hn : n < schedule.events.length
  · rw [lazyCache_succ_of_lt k V schedule hn]
    exact card_sdiff_lazyStep_le k V _ _
  · rw [lazyCache_succ_of_le k V schedule (Nat.le_of_not_lt hn)]
    simp

/-- An event that evicts a page has inserted a page of the universe that was
absent before. -/
theorem exists_fetched_of_evicted (n : ℕ) {p : Page}
    (hp : p ∈ lazyCache k V schedule n) (hp' : p ∉ lazyCache k V schedule (n + 1)) :
    ∃ f ∈ V, f ∉ lazyCache k V schedule n ∧ f ∈ lazyCache k V schedule (n + 1) := by
  by_cases hn : n < schedule.events.length
  · rw [lazyCache_succ_of_lt k V schedule hn] at hp' ⊢
    obtain ⟨hV, hnot, hmem⟩ := exists_fetched_of_lazyStep_evicts k V _ _ hp hp'
    exact ⟨_, hV, hnot, hmem⟩
  · rw [lazyCache_succ_of_le k V schedule (Nat.le_of_not_lt hn)] at hp'
    exact absurd hp hp'

/-- The page evicted by event `n`, if any, is the only one: the eviction set
is contained in the singleton of any of its members. -/
theorem sdiff_lazyCache_succ_subset_singleton (n : ℕ) {p : Page}
    (hp : p ∈ lazyCache k V schedule n) (hp' : p ∉ lazyCache k V schedule (n + 1)) :
    lazyCache k V schedule n \ lazyCache k V schedule (n + 1) ⊆ {p} := by
  have hmem : p ∈ lazyCache k V schedule n \ lazyCache k V schedule (n + 1) :=
    Finset.mem_sdiff.mpr ⟨hp, hp'⟩
  have hcard := card_sdiff_lazyCache_succ_le (k := k) (V := V) (schedule := schedule) n
  intro q hq
  rw [Finset.mem_singleton]
  exact Finset.card_le_one.mp hcard q hq p hmem

/-- Two pages evicted by the same event are the same page. -/
theorem eq_of_evicted_at (n : ℕ) {p q : Page}
    (hp : p ∈ lazyCache k V schedule n) (hp' : p ∉ lazyCache k V schedule (n + 1))
    (hq : q ∈ lazyCache k V schedule n) (hq' : q ∉ lazyCache k V schedule (n + 1)) : p = q :=
  (Finset.mem_singleton.mp
    (sdiff_lazyCache_succ_subset_singleton n hq hq' (Finset.mem_sdiff.mpr ⟨hp, hp'⟩)))

end

end PagingWithDelay.Analysis
