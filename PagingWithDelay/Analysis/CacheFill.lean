import PagingWithDelay.Model

/-!
# Installing a prescribed cache

Offline comparisons often start with a prescribed cache. `fillEvents` installs
a list of pages with one fetch per page, all at time zero, using the trusted
transition semantics, and `resetEvents` turns the initial cache an instance
supplies into any target cache by fetching only the pages it lacks.  The
lemmas below account for this finite startup cost.
-/

namespace PagingWithDelay.Analysis

variable {Page : Type*} [DecidableEq Page]

theorem validTransitions_append (first second : List (FetchEvent Page))
    (initial : Finset Page)
    (hfirst : Schedule.ValidTransitionsFrom initial first)
    (hsecond : Schedule.ValidTransitionsFrom
      (first.foldl (fun _ event => event.cacheAfter) initial) second) :
    Schedule.ValidTransitionsFrom initial (first ++ second) := by
  induction first generalizing initial with
  | nil => exact hsecond
  | cons event rest ih =>
      exact ⟨hfirst.1, hfirst.2.1, ih _ hfirst.2.2 hsecond⟩

/-- Install a list of pages, retaining the previously installed pages. -/
def fillEvents (initial : Finset Page) : List Page → List (FetchEvent Page)
  | [] => []
  | page :: rest =>
      ⟨0, page, insert page initial⟩ :: fillEvents (insert page initial) rest

@[simp] theorem fillEvents_length (initial : Finset Page) (pages : List Page) :
    (fillEvents initial pages).length = pages.length := by
  induction pages generalizing initial with
  | nil => rfl
  | cons page rest ih => simp [fillEvents, ih]

theorem fillEvents_time (initial : Finset Page) (pages : List Page)
    (event : FetchEvent Page) (he : event ∈ fillEvents initial pages) : event.time = 0 := by
  induction pages generalizing initial with
  | nil => simp [fillEvents] at he
  | cons page rest ih =>
      rcases List.mem_cons.mp he with rfl | he
      · rfl
      · exact ih _ he

theorem fillEvents_valid (initial : Finset Page) (pages : List Page)
    (hnodup : pages.Nodup) (hnew : ∀ page ∈ pages, page ∉ initial) :
    Schedule.ValidTransitionsFrom initial (fillEvents initial pages) := by
  induction pages generalizing initial with
  | nil => trivial
  | cons page rest ih =>
      have hp := hnew page (by simp)
      have hnd := List.nodup_cons.mp hnodup
      refine ⟨by simp, ?_, ih _ hnd.2 ?_⟩
      · ext p
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        aesop
      · intro p hrest
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun heq => hnd.1 (heq ▸ hrest), hnew p (by simp [hrest])⟩

/-- The fill may start from a *sub*set of the actual previous cache: the first
fetch then also evicts the pages outside `base`. -/
theorem fillEvents_valid_of_subset {base initial : Finset Page} (hbase : base ⊆ initial)
    (pages : List Page) (hnodup : pages.Nodup) (hnew : ∀ page ∈ pages, page ∉ initial) :
    Schedule.ValidTransitionsFrom initial (fillEvents base pages) := by
  cases pages with
  | nil => trivial
  | cons page rest =>
      have hp := hnew page (by simp)
      have hnd := List.nodup_cons.mp hnodup
      refine ⟨by simp, ?_, ?_⟩
      · ext p
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | hp', hnot⟩
          · rfl
          · exact absurd (hbase hp') hnot
        · rintro rfl
          exact ⟨Or.inl rfl, hp⟩
      · refine fillEvents_valid _ _ hnd.2 ?_
        intro p hrest
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun heq => hnd.1 (heq ▸ hrest), fun hb => hnew p (by simp [hrest]) (hbase hb)⟩

theorem fillEvents_cache_subset (initial : Finset Page) (pages : List Page)
    (event : FetchEvent Page) (he : event ∈ fillEvents initial pages) :
    event.cacheAfter ⊆ initial ∪ pages.toFinset := by
  induction pages generalizing initial with
  | nil => simp [fillEvents] at he
  | cons page rest ih =>
      rcases List.mem_cons.mp he with rfl | he
      · simp only [List.toFinset_cons]
        intro p hp
        simp only [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · simp
        · exact Finset.mem_union_left _ hp
      · have h := ih _ he
        simpa [List.toFinset_cons, Finset.insert_union] using h

/-- After all fill events, the initial cache and all listed pages are held. -/
theorem fillEvents_fold (initial : Finset Page) (pages : List Page) :
    (fillEvents initial pages).foldl (fun _ event => event.cacheAfter) initial =
      initial ∪ pages.toFinset := by
  induction pages generalizing initial with
  | nil => simp [fillEvents]
  | cons page rest ih =>
      simpa [fillEvents, List.toFinset_cons, Finset.insert_union] using
        ih (insert page initial)

/-! ## Resetting an initial cache to a target -/

/-- Turn the cache `initial` into `target`, at time zero, fetching exactly the
pages of `target` outside `initial`; the first fetch also evicts the pages of
`initial` outside `target`. -/
noncomputable def resetEvents (initial target : Finset Page) : List (FetchEvent Page) :=
  fillEvents (initial ∩ target) (target \ initial).toList

private theorem inter_union_sdiff' (initial target : Finset Page) :
    initial ∩ target ∪ target \ initial = target := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem resetEvents_time (initial target : Finset Page)
    (event : FetchEvent Page) (he : event ∈ resetEvents initial target) : event.time = 0 :=
  fillEvents_time _ _ event he

theorem resetEvents_valid (initial target : Finset Page) :
    Schedule.ValidTransitionsFrom initial (resetEvents initial target) :=
  fillEvents_valid_of_subset Finset.inter_subset_left _ (Finset.nodup_toList _)
    (fun _ hpage => (Finset.mem_sdiff.mp (Finset.mem_toList.mp hpage)).2)

theorem resetEvents_cache_subset (initial target : Finset Page)
    (event : FetchEvent Page) (he : event ∈ resetEvents initial target) :
    event.cacheAfter ⊆ target := by
  refine (fillEvents_cache_subset _ _ event he).trans ?_
  rw [Finset.toList_toFinset, inter_union_sdiff']

/-- After the reset the target is held.  When nothing needs fetching the cache
is untouched, so the initial cache must be no larger than the target for it to
be the target already. -/
theorem resetEvents_fold (initial target : Finset Page) (hcard : initial.card ≤ target.card) :
    (resetEvents initial target).foldl (fun _ event => event.cacheAfter) initial = target := by
  have h : ∀ (events : List (FetchEvent Page)) (a b : Finset Page), events ≠ [] →
      events.foldl (fun _ event => event.cacheAfter) a =
        events.foldl (fun _ event => event.cacheAfter) b := by
    intro events a b hne
    cases events with
    | nil => exact absurd rfl hne
    | cons e rest => rfl
  by_cases hempty : (target \ initial).toList = []
  · have hsub : target ⊆ initial := by
      intro p hp
      by_contra hnot
      have : p ∈ (target \ initial).toList := Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨hp, hnot⟩)
      simp [hempty] at this
    rw [resetEvents, hempty, fillEvents, List.foldl_nil]
    exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
  · have hne : fillEvents (initial ∩ target) (target \ initial).toList ≠ [] := by
      intro hnil
      have := congrArg List.length hnil
      rw [fillEvents_length] at this
      exact hempty (List.length_eq_zero_iff.mp this)
    rw [resetEvents, h _ initial (initial ∩ target) hne, fillEvents_fold, Finset.toList_toFinset,
      inter_union_sdiff']

theorem resetEvents_length_le (initial target : Finset Page) :
    (resetEvents initial target).length ≤ target.card := by
  rw [resetEvents, fillEvents_length, Finset.length_toList]
  exact Finset.card_le_card Finset.sdiff_subset


/-- The reset fetches exactly the pages of the target outside the initial cache. -/
theorem resetEvents_length (initial target : Finset Page) :
    (resetEvents initial target).length = (target \ initial).card := by
  rw [resetEvents, fillEvents_length, Finset.length_toList]

/-- Nothing to reset when the target is the initial cache. -/
@[simp] theorem resetEvents_self (cache : Finset Page) : resetEvents cache cache = [] := by
  rw [← List.length_eq_zero_iff, resetEvents_length, Finset.sdiff_self, Finset.card_empty]

end PagingWithDelay.Analysis
