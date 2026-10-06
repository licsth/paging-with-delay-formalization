import Model

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
      exacts [rfl, ih _ he]

/-- The fill may start from a *sub*set `base` of the actual previous cache: the
first fetch then also evicts the pages outside `base`. -/
theorem fillEvents_valid_of_subset {base initial : Finset Page} (hbase : base ⊆ initial)
    (pages : List Page) (hnodup : pages.Nodup) (hnew : ∀ page ∈ pages, page ∉ initial) :
    Schedule.ValidTransitionsFrom initial (fillEvents base pages) := by
  induction pages generalizing base initial with
  | nil => trivial
  | cons page rest ih =>
      have hp := hnew page (by simp)
      have hnd := List.nodup_cons.mp hnodup
      refine ⟨by simp, ?_, ih subset_rfl hnd.2 fun p hrest => ?_⟩
      · ext p
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun ⟨h, hnot⟩ => h.resolve_right fun h' => hnot (hbase h'),
          fun h => ⟨.inl h, h ▸ hp⟩⟩
      · simp only [Finset.mem_insert, not_or]
        exact ⟨fun heq => hnd.1 (heq ▸ hrest), fun hb => hnew p (by simp [hrest]) (hbase hb)⟩

theorem fillEvents_cache_subset (initial : Finset Page) (pages : List Page)
    (event : FetchEvent Page) (he : event ∈ fillEvents initial pages) :
    event.cacheAfter ⊆ initial ∪ pages.toFinset := by
  induction pages generalizing initial with
  | nil => simp [fillEvents] at he
  | cons page rest ih =>
      rcases List.mem_cons.mp he with rfl | he
      · rw [List.toFinset_cons, Finset.union_insert]
        exact Finset.insert_subset_insert _ Finset.subset_union_left
      · simpa [Finset.insert_union] using ih _ he

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
  have hunion := inter_union_sdiff' initial target
  rw [← Finset.toList_toFinset (target \ initial)] at hunion
  unfold resetEvents
  cases hlist : (target \ initial).toList with
  | nil =>
      have hsub := Finset.sdiff_eq_empty_iff_subset.mp (Finset.toList_eq_nil.mp hlist)
      exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
  | cons page rest =>
      rw [hlist] at hunion
      simpa [fillEvents, fillEvents_fold, Finset.insert_union] using hunion

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
