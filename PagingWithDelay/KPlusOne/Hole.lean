import PagingWithDelay.KPlusOne.Window
import PagingWithDelay.Analysis.CacheTrace
import PagingWithDelay.Analysis.Rank

/-!
# The comparator's hole

With `k + 1` pages and a cache of `k`, the comparator is missing at least one
page of the universe at every moment.  `hole` picks one such page after each of
its events, changing only when the page it names is fetched.

This is the device that lets the potential argument of Section 5 read the
comparator through a single page: the paper's potential
`∑_{q ∈ FIFO ∩ OPT} rank q` equals `K - rank (hole)`, because FIFO's cache is
the universe minus the page it is about to fetch.

Working with a *chosen* missing page rather than the comparator's actual cache
also makes the argument immune to a comparator that evicts more pages than it
must: the hole moves at most once per event by construction.
-/

namespace PagingWithDelay.KPlusOne

open PagingWithDelay

variable {Page : Type*} [DecidableEq Page]

namespace Setup

noncomputable section

variable (S : Setup Page)

/-- Some page of the universe outside a cache of at most `k` pages. -/
def missingPage (cache : Finset Page) : Page :=
  if h : (S.pages \ cache).Nonempty then h.choose else S.somePage

theorem missingPage_spec {cache : Finset Page} (hcard : cache.card ≤ S.cacheSize) :
    S.missingPage cache ∈ S.pages ∧ S.missingPage cache ∉ cache := by
  have hne : (S.pages \ cache).Nonempty := by
    apply Finset.card_pos.mp
    have hle := Finset.le_card_sdiff cache S.pages
    rw [S.card] at hle
    omega
  rw [missingPage, dif_pos hne]
  have hmem := hne.choose_spec
  exact ⟨(Finset.mem_sdiff.mp hmem).1, (Finset.mem_sdiff.mp hmem).2⟩

end

end Setup

/-- A page of the universe that the comparator does not hold after its first
`n` events.  It only moves when the comparator fetches it. -/
noncomputable def hole (S : Setup Page) (comparator : Schedule Page) : ℕ → Page
  | 0 => S.missingPage ∅
  | n + 1 =>
      if hole S comparator n ∈ Analysis.cacheAfterCount comparator (n + 1) then
        S.missingPage (Analysis.cacheAfterCount comparator (n + 1))
      else hole S comparator n

variable {S : Setup Page} {comparator : Schedule Page}

/-- The defining property of the hole: it is a page of the universe, and the
comparator does not hold it. -/
theorem hole_spec (feasible : comparator.Feasible S.input) (n : ℕ) :
    hole S comparator n ∈ S.pages ∧
      hole S comparator n ∉ Analysis.cacheAfterCount comparator n := by
  have hcard : ∀ m : ℕ, (Analysis.cacheAfterCount comparator m).card ≤ S.cacheSize := by
    intro m
    rw [← S.size]
    exact Analysis.cacheAfterCount_card_le comparator S.input feasible.capacity m
  induction n with
  | zero =>
      have := S.missingPage_spec (cache := ∅) (by simp)
      simpa [hole] using this
  | succ n ih =>
      rw [hole]
      split
      · exact S.missingPage_spec (hcard (n + 1))
      · rename_i hnot
        exact ⟨ih.1, hnot⟩

theorem hole_mem_pages (feasible : comparator.Feasible S.input) (n : ℕ) :
    hole S comparator n ∈ S.pages := (hole_spec feasible n).1

theorem hole_notMem_cache (feasible : comparator.Feasible S.input) (n : ℕ) :
    hole S comparator n ∉ Analysis.cacheAfterCount comparator n := (hole_spec feasible n).2

end PagingWithDelay.KPlusOne
