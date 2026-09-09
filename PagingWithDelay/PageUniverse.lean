import PagingWithDelay.Model

/-!
# The page universe of an instance

`Model.lean` defines `Instance.pageUniverse` as the finite set of requested
pages. The statements restricted to a small universe bound its cardinality;
these lemmas translate between that bound and the membership form used inside
the proofs.
-/

namespace PagingWithDelay

namespace Instance

variable {Page : Type*} [DecidableEq Page]

@[simp] theorem mem_pageUniverse {input : Instance Page} {page : Page} :
    page ∈ input.pageUniverse ↔ ∃ request ∈ input.requests, request.page = page := by
  simp [pageUniverse]

theorem pageUniverse_subset_iff {input : Instance Page} {pages : Finset Page} :
    input.pageUniverse ⊆ pages ↔ ∀ request ∈ input.requests, request.page ∈ pages := by
  constructor
  · intro h request hrequest
    exact h (mem_pageUniverse.mpr ⟨request, hrequest, rfl⟩)
  · intro h page hpage
    obtain ⟨request, hrequest, rfl⟩ := mem_pageUniverse.mp hpage
    exact h request hrequest

/-- Requesting only pages of a finite set bounds the universe by its size. -/
theorem card_pageUniverse_le {input : Instance Page} {pages : Finset Page}
    (h : ∀ request ∈ input.requests, request.page ∈ pages) :
    input.pageUniverse.card ≤ pages.card :=
  Finset.card_le_card (pageUniverse_subset_iff.mpr h)

/-- Conversely, an instance using at most `n` pages of a type with at least `n`
pages can be given a universe of exactly `n` pages.  This is what makes the
cardinality bound equivalent to naming a set of that size beforehand. -/
theorem exists_universe_card_eq {input : Instance Page} {n : ℕ} (pages : Fin n ↪ Page)
    (h : input.pageUniverse.card ≤ n) :
    ∃ cover : Finset Page, cover.card = n ∧
      ∀ request ∈ input.requests, request.page ∈ cover := by
  have hcard : ((Finset.univ.map pages).card) = n := by simp
  have hle : n ≤ (input.pageUniverse ∪ Finset.univ.map pages).card := by
    calc n = (Finset.univ.map pages).card := hcard.symm
      _ ≤ _ := Finset.card_le_card Finset.subset_union_right
  obtain ⟨cover, hsubset, _, hcover⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_union_left
      (s₁ := input.pageUniverse) (s₂ := Finset.univ.map pages)) h hle
  exact ⟨cover, hcover, pageUniverse_subset_iff.mp hsubset⟩

end Instance

end PagingWithDelay
