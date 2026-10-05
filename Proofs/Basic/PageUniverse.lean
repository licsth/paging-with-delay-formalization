import Model

/-!
# The page universe of an instance

`Model.lean` defines `Instance.pageUniverse` as the finite set of pages an
instance involves: those in its initial cache and those it requests. The
statements restricted to a small universe bound its cardinality; these lemmas
translate between that bound and the membership form used inside the proofs.
-/

namespace PagingWithDelay

namespace Instance

variable {Page : Type*} [DecidableEq Page]

@[simp] theorem mem_pageUniverse {input : Instance Page} {page : Page} :
    page ∈ input.pageUniverse ↔
      page ∈ input.initialCache ∨ ∃ request ∈ input.requests, request.page = page := by
  simp [pageUniverse]

theorem pageUniverse_subset_iff {input : Instance Page} {pages : Finset Page} :
    input.pageUniverse ⊆ pages ↔
      (∀ page ∈ input.initialCache, page ∈ pages) ∧
        ∀ request ∈ input.requests, request.page ∈ pages := by
  constructor
  · intro h
    exact ⟨fun page hpage => h (mem_pageUniverse.mpr (Or.inl hpage)),
      fun request hrequest => h (mem_pageUniverse.mpr (Or.inr ⟨request, hrequest, rfl⟩))⟩
  · intro h page hpage
    rcases mem_pageUniverse.mp hpage with hinitial | ⟨request, hrequest, rfl⟩
    · exact h.1 page hinitial
    · exact h.2 request hrequest

/-- Drawing the initial cache and every request from a finite set bounds the
universe by its size. -/
theorem card_pageUniverse_le {input : Instance Page} {pages : Finset Page}
    (hinitial : ∀ page ∈ input.initialCache, page ∈ pages)
    (h : ∀ request ∈ input.requests, request.page ∈ pages) :
    input.pageUniverse.card ≤ pages.card :=
  Finset.card_le_card (pageUniverse_subset_iff.mpr ⟨hinitial, h⟩)

/-- Conversely, an instance using at most `n` pages of a type with at least `n`
pages can be given a universe of exactly `n` pages.  This is what makes the
cardinality bound equivalent to naming a set of that size beforehand. -/
theorem exists_universe_card_eq {input : Instance Page} {n : ℕ} (pages : Fin n ↪ Page)
    (h : input.pageUniverse.card ≤ n) :
    ∃ cover : Finset Page, cover.card = n ∧
      (∀ page ∈ input.initialCache, page ∈ cover) ∧
      ∀ request ∈ input.requests, request.page ∈ cover := by
  have hcard : ((Finset.univ.map pages).card) = n := by simp
  have hle : n ≤ (input.pageUniverse ∪ Finset.univ.map pages).card := by
    calc n = (Finset.univ.map pages).card := hcard.symm
      _ ≤ _ := Finset.card_le_card Finset.subset_union_right
  obtain ⟨cover, hsubset, _, hcover⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_union_left
      (s₁ := input.pageUniverse) (s₂ := Finset.univ.map pages)) h hle
  exact ⟨cover, hcover, pageUniverse_subset_iff.mp hsubset⟩

/-- The initial cache lies in the universe. -/
theorem initialCache_subset_pageUniverse (input : Instance Page) :
    input.initialCache.toFinset ⊆ input.pageUniverse := by
  intro page hpage
  exact mem_pageUniverse.mpr (Or.inl (List.mem_toFinset.mp hpage))

/-- On a instance the universe has at least `cacheSize` pages. -/
theorem cacheSize_le_card_pageUniverse {input : Instance Page} :
    input.cacheSize ≤ input.pageUniverse.card := by
  calc input.cacheSize = input.initialCache.length := input.initialCache_full.symm
    _ = input.initialCache.toFinset.card :=
        (List.toFinset_card_of_nodup input.initialCache_nodup).symm
    _ ≤ input.pageUniverse.card :=
        Finset.card_le_card (initialCache_subset_pageUniverse input)

end Instance

end PagingWithDelay
