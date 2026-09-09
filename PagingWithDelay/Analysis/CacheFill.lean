import PagingWithDelay.Model

/-!
# Filling an initially empty cache

Offline comparisons often start with a prescribed cache. `fillEvents` installs
it with one fetch per page, all at time zero, using the trusted transition
semantics. The lemmas below account for this finite startup cost.
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

end PagingWithDelay.Analysis
