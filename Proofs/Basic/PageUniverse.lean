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
  simp [Finset.subset_iff, or_imp, forall_and]

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
  have hle : n ≤ (input.pageUniverse ∪ Finset.univ.map pages).card :=
    (by simp : (Finset.univ.map pages).card = n).ge.trans
      (Finset.card_le_card Finset.subset_union_right)
  obtain ⟨cover, hsubset, _, hcover⟩ :=
    Finset.exists_subsuperset_card_eq Finset.subset_union_left h hle
  exact ⟨cover, hcover, pageUniverse_subset_iff.mp hsubset⟩

end Instance

end PagingWithDelay
