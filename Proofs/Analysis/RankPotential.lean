import Proofs.Analysis.Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The rank potential

The complement of the write-up's potential for comparing a FIFO cache with an
offline cache:

  `K - Φ = ∑_{q ∈ C_ALG ∩ C_OPT} rank q`,

where `rank` is the position in the FIFO queue, `1` for the page evicted next
and `k` for the page fetched last.  `rankPotential queue cache` is that sum for
a FIFO queue `queue` (a list, oldest page first) and an offline cache `cache`.

The lemmas are the write-up's "Potential changes", in complement form
(here `Φ` denotes the sum above):

* `rankPotential_le_triangular`: `0 ≤ Φ ≤ K = k(k+1)/2`, with equality when the
  caches coincide (`rankPotential_toFinset`);
* `rankPotential_fifo_step`: at a FIFO payment `Φ' = Φ - m + k·[p ∈ C_OPT]`,
  where `m = |C_ALG ∩ C_OPT|` before the payment;
* `rankPotential_le_of_sdiff_subset_singleton`: at an offline fetch that
  evicts at most one page `e`, `Φ ≥ Φ_before - rank e`, so `Φ` drops by at
  most `k`, and not at all when `e` is outside the FIFO queue.

The write-up itself uses the complementary potential
`Φ = ∑_{q ∈ C_ALG \ C_OPT} rank q`, with `Φ_0 = 0`.  It is `missingPotential`,
equal to `K - rankPotential` (`missingPotential_add_rankPotential`); the
lemmas at the end of this file restate the potential changes for it, with the
signs of the write-up (`ΔΦ ≤ k` at an offline fetch, `ΔΦ = m - k·[p ∈ C_OPT]`
at a payment).

These are pure list and finset facts about `rank`, reusable for any FIFO
potential argument.
-/

namespace PagingWithDelay.Analysis

open Finset

variable {α : Type*} [DecidableEq α]

/-- The pages of the FIFO queue that the offline cache also holds. -/
def sharedPages (queue : List α) (cache : Finset α) : Finset α :=
  queue.toFinset ∩ cache

/-- `∑_{q ∈ queue ∩ cache} rank queue q`. -/
def rankPotential (queue : List α) (cache : Finset α) : ℕ :=
  ∑ q ∈ sharedPages queue cache, rank queue q

/-- The maximal potential for a queue of length `k`: `1 + 2 + ⋯ + k`. -/
def triangular (k : ℕ) : ℕ := ∑ j ∈ Finset.range k, (j + 1)

/-! ### Monotonicity and splitting in the offline cache -/

theorem rankPotential_mono (queue : List α) {cache cache' : Finset α} (h : cache ⊆ cache') :
    rankPotential queue cache ≤ rankPotential queue cache' :=
  Finset.sum_le_sum_of_subset (Finset.inter_subset_inter_left h)

theorem rankPotential_union_le (queue : List α) (cache cache' : Finset α) :
    rankPotential queue (cache ∪ cache') ≤
      rankPotential queue cache + rankPotential queue cache' := by
  unfold rankPotential sharedPages
  rw [Finset.inter_union_distrib_left]
  have := Finset.sum_union_inter (s₁ := queue.toFinset ∩ cache) (s₂ := queue.toFinset ∩ cache')
    (f := rank queue)
  omega

theorem rankPotential_singleton_le (queue : List α) (page : α) :
    rankPotential queue {page} ≤ rank queue page := by
  unfold rankPotential sharedPages
  by_cases h : page ∈ queue
  · rw [Finset.inter_singleton_of_mem (List.mem_toFinset.mpr h), Finset.sum_singleton]
  · rw [Finset.inter_singleton_of_notMem (fun hm => h (List.mem_toFinset.mp hm))]
    simp

/-- **Potential changes at an offline fetch.**  If the offline cache changes
from `cache` to `cache'` evicting at most the page `evicted`, the potential
drops by at most `rank queue evicted` — at most `k`, and not at all when the
evicted page is outside the FIFO queue. -/
theorem rankPotential_le_of_sdiff_subset_singleton (queue : List α)
    {cache cache' : Finset α} {evicted : α} (h : cache \ cache' ⊆ {evicted}) :
    rankPotential queue cache ≤ rankPotential queue cache' + rank queue evicted := by
  calc rankPotential queue cache
      ≤ rankPotential queue (cache' ∪ {evicted}) := by
        apply rankPotential_mono
        intro q hq
        by_cases hq' : q ∈ cache'
        · exact Finset.mem_union_left _ hq'
        · exact Finset.mem_union_right _ (h (Finset.mem_sdiff.mpr ⟨hq, hq'⟩))
    _ ≤ rankPotential queue cache' + rankPotential queue {evicted} :=
        rankPotential_union_le _ _ _
    _ ≤ rankPotential queue cache' + rank queue evicted :=
        Nat.add_le_add_left (rankPotential_singleton_le _ _) _

/-- An offline fetch that evicts at most one page drops `Φ` by at most `k`. -/
theorem rankPotential_le_add_length_of_card_sdiff_le_one (queue : List α)
    {cache cache' : Finset α} (h : (cache \ cache').card ≤ 1) :
    rankPotential queue cache ≤ rankPotential queue cache' + queue.length := by
  rcases Nat.lt_or_ge (cache \ cache').card 1 with hlt | hge
  · have hempty : cache \ cache' = ∅ := Finset.card_eq_zero.mp (by omega)
    exact (rankPotential_mono queue (Finset.sdiff_eq_empty_iff_subset.mp hempty)).trans
      (Nat.le_add_right _ _)
  · obtain ⟨evicted, hevicted⟩ := Finset.card_eq_one.mp (le_antisymm h hge)
    exact (rankPotential_le_of_sdiff_subset_singleton queue hevicted.le).trans
      (Nat.add_le_add_left (rank_le_length _ _) _)

/-- Removing a page outside the FIFO queue from the offline cache changes
nothing. -/
theorem rankPotential_erase_of_not_mem (queue : List α) (cache : Finset α) {page : α}
    (hpage : page ∉ queue) :
    rankPotential queue (cache.erase page) = rankPotential queue cache := by
  unfold rankPotential sharedPages
  rw [← Finset.erase_inter_comm, Finset.erase_eq_of_notMem (by simpa using hpage)]

/-- Adding a page of the FIFO queue to the offline cache adds its rank. -/
theorem rankPotential_insert_of_mem (queue : List α) {cache : Finset α} {page : α}
    (hnot : page ∉ cache) (hmem : page ∈ queue) :
    rankPotential queue (insert page cache) = rankPotential queue cache + rank queue page := by
  unfold rankPotential sharedPages
  rw [Finset.inter_insert_of_mem (List.mem_toFinset.mpr hmem),
    Finset.sum_insert (fun h => hnot (Finset.mem_inter.mp h).2), add_comm]

/-! ### The maximal potential -/

/-- Over the whole queue the ranks sum to `1 + ⋯ + k`. -/
theorem sum_rank_toFinset {queue : List α} (hnodup : queue.Nodup) :
    ∑ q ∈ queue.toFinset, rank queue q = triangular queue.length := by
  induction queue with
  | nil => simp [triangular]
  | cons head tail ih =>
      rw [List.nodup_cons] at hnodup
      have hcongr : ∀ q ∈ tail.toFinset, rank (head :: tail) q = rank tail q + 1 :=
        fun q hq => rank_cons_of_mem (List.mem_toFinset.mp hq)
          (by rintro rfl; exact hnodup.1 (List.mem_toFinset.mp hq))
      rw [List.toFinset_cons, Finset.sum_insert (fun h => hnodup.1 (List.mem_toFinset.mp h)),
        rank_cons_self, Finset.sum_congr rfl hcongr,
        Finset.sum_add_distrib, ih hnodup.2, Finset.sum_const,
        List.toFinset_card_of_nodup hnodup.2, List.length_cons, triangular, triangular,
        Finset.sum_range_succ]
      simp only [nsmul_eq_mul, Nat.cast_id, mul_one]
      omega

/-- Both caches equal: the potential is maximal. -/
theorem rankPotential_toFinset {queue : List α} (hnodup : queue.Nodup) :
    rankPotential queue queue.toFinset = triangular queue.length := by
  unfold rankPotential sharedPages
  rw [Finset.inter_self]
  exact sum_rank_toFinset hnodup

/-- `Φ ≤ K`. -/
theorem rankPotential_le_triangular {queue : List α} (hnodup : queue.Nodup) (cache : Finset α) :
    rankPotential queue cache ≤ triangular queue.length := by
  rw [← sum_rank_toFinset hnodup]
  exact Finset.sum_le_sum_of_subset Finset.inter_subset_left

/-! ### The FIFO step -/

theorem sharedPages_card_le (queue : List α) (cache : Finset α) :
    (sharedPages queue cache).card ≤ queue.length :=
  (Finset.card_le_card Finset.inter_subset_left).trans (List.toFinset_card_le _)

/-- A page of the offline cache outside the FIFO queue leaves room: fewer than
`|cache|` pages are shared. -/
theorem sharedPages_card_lt (queue : List α) {cache : Finset α} {page : α}
    (hmem : page ∈ cache) (hnot : page ∉ queue) :
    (sharedPages queue cache).card < cache.card := by
  apply Finset.card_lt_card
  refine ⟨Finset.inter_subset_right, ?_⟩
  intro h
  exact hnot (List.mem_toFinset.mp (Finset.mem_inter.mp (h hmem)).1)

/-- Splitting off a page `x` outside `tail` from a queue holding the pages of
`tail` and `x`. -/
private theorem sum_sharedPages_insert {queue tail : List α} {x : α}
    (hqueue : queue.toFinset = insert x tail.toFinset) (hx : x ∉ tail) (cache : Finset α)
    (f : α → ℕ) :
    ∑ q ∈ sharedPages queue cache, f q =
      ∑ q ∈ sharedPages tail cache, f q + if x ∈ cache then f x else 0 := by
  unfold sharedPages
  rw [hqueue]
  split_ifs with h
  · rw [Finset.insert_inter_of_mem h, Finset.sum_insert (by simp [hx]), add_comm]
  · rw [Finset.insert_inter_of_notMem h, add_zero]

/-- **Potential changes at a FIFO payment.**  Evicting the front of the queue
and fetching `page` at the back turns `Φ` into `Φ - m + k·[page ∈ cache]`,
where `m` is the number of shared pages before the payment and `k` the queue
length.  Stated additively in `ℕ`. -/
theorem rankPotential_fifo_step {queue : List α} (hnodup : queue.Nodup) (hne : queue ≠ [])
    {page : α} (hpage : page ∉ queue) (cache : Finset α) :
    rankPotential (queue.tail ++ [page]) cache + (sharedPages queue cache).card =
      rankPotential queue cache + (if page ∈ cache then queue.length else 0) := by
  cases queue with
  | nil => exact absurd rfl hne
  | cons head tail =>
      rw [List.nodup_cons] at hnodup
      have hpt : page ∉ tail := fun h => hpage (List.mem_cons_of_mem _ h)
      have hmem : ∀ q ∈ sharedPages tail cache, q ∈ tail :=
        fun q hq => List.mem_toFinset.mp (Finset.mem_inter.mp hq).1
      -- ranks of the pages of `tail`: unchanged in the new queue, one more in the old one
      have hrank_new : ∀ q ∈ sharedPages tail cache, rank (tail ++ [page]) q = rank tail q :=
        fun q hq => rank_append_of_mem (hmem q hq)
      have hrank_old : ∀ q ∈ sharedPages tail cache, rank (head :: tail) q = rank tail q + 1 :=
        fun q hq => rank_cons_of_mem (hmem q hq) (by rintro rfl; exact hnodup.1 (hmem q hq))
      have hnew : (tail ++ [page]).toFinset = insert page tail.toFinset := by
        rw [List.toFinset_append, Finset.union_comm]; rfl
      unfold rankPotential
      rw [List.tail_cons, List.length_cons, sum_sharedPages_insert hnew hpt,
        sum_sharedPages_insert List.toFinset_cons hnodup.1, Finset.card_eq_sum_ones,
        sum_sharedPages_insert List.toFinset_cons hnodup.1,
        Finset.sum_congr rfl hrank_new, Finset.sum_congr rfl hrank_old, Finset.sum_add_distrib,
        rank_append_self hpt, rank_cons_self]
      have heta : (sharedPages tail cache).sum (rank tail) =
          ∑ q ∈ sharedPages tail cache, rank tail q := rfl
      split_ifs <;> omega

/-! ### The write-up's potential over the complement

The write-up now measures the pages of FIFO's cache that the offline cache
*lacks*: `Φ = ∑_{q ∈ C_ALG \ C_OPT} rank q`, which starts at `0`.  The ranks
of a full queue sum to `K = k(k+1)/2`, so this is `K - rankPotential`
(`missingPotential_add_rankPotential`), and every statement about one is a
statement about the other.  The lemmas below restate "Potential changes" in
the write-up's direction. -/

/-- The pages of the FIFO queue that the offline cache does not hold. -/
def missingPages (queue : List α) (cache : Finset α) : Finset α :=
  queue.toFinset \ cache

/-- The write-up's rank potential `∑_{q ∈ C_ALG \ C_OPT} rank queue q`. -/
def missingPotential (queue : List α) (cache : Finset α) : ℕ :=
  ∑ q ∈ missingPages queue cache, rank queue q

/-- The two potentials are complementary: `Φ_missing + Φ_shared = K`. -/
theorem missingPotential_add_rankPotential {queue : List α} (hnodup : queue.Nodup)
    (cache : Finset α) :
    missingPotential queue cache + rankPotential queue cache = triangular queue.length := by
  unfold missingPotential missingPages rankPotential sharedPages
  rw [← Finset.sdiff_inter_self_left,
    Finset.sum_sdiff Finset.inter_subset_left, sum_rank_toFinset hnodup]

/-- Both caches equal: the write-up's potential is `0`. -/
theorem missingPotential_toFinset (queue : List α) :
    missingPotential queue queue.toFinset = 0 := by
  simp [missingPotential, missingPages]

/-- `Φ ≤ K`. -/
theorem missingPotential_le_triangular {queue : List α} (hnodup : queue.Nodup)
    (cache : Finset α) : missingPotential queue cache ≤ triangular queue.length := by
  have := missingPotential_add_rankPotential hnodup cache
  omega

/-- **Potential changes at an offline fetch**, write-up direction: evicting at
most the page `evicted` raises `Φ` by at most `rank queue evicted` — at most
`k`, and not at all when the evicted page is outside the FIFO queue. -/
theorem missingPotential_le_of_sdiff_subset_singleton {queue : List α} (hnodup : queue.Nodup)
    {cache cache' : Finset α} {evicted : α} (h : cache \ cache' ⊆ {evicted}) :
    missingPotential queue cache' ≤ missingPotential queue cache + rank queue evicted := by
  have := rankPotential_le_of_sdiff_subset_singleton queue h
  have h1 := missingPotential_add_rankPotential hnodup cache
  have h2 := missingPotential_add_rankPotential hnodup cache'
  omega

/-- An offline fetch that evicts at most one page raises `Φ` by at most `k`. -/
theorem missingPotential_le_add_length_of_card_sdiff_le_one {queue : List α}
    (hnodup : queue.Nodup) {cache cache' : Finset α} (h : (cache \ cache').card ≤ 1) :
    missingPotential queue cache' ≤ missingPotential queue cache + queue.length := by
  have := rankPotential_le_add_length_of_card_sdiff_le_one queue h
  have h1 := missingPotential_add_rankPotential hnodup cache
  have h2 := missingPotential_add_rankPotential hnodup cache'
  omega

/-- **Potential changes at a FIFO payment**, write-up direction:
`Φ' = Φ + m - k·[page ∈ cache]`, with `m = |C_ALG ∩ C_OPT|` before the payment
(equation `ΔΦ = m - k·𝟙[v_i ∈ C_OPT]`).  Stated additively in `ℕ`. -/
theorem missingPotential_fifo_step {queue : List α} (hnodup : queue.Nodup) (hne : queue ≠ [])
    {page : α} (hpage : page ∉ queue) (cache : Finset α) :
    missingPotential (queue.tail ++ [page]) cache +
        (if page ∈ cache then queue.length else 0) =
      missingPotential queue cache + (sharedPages queue cache).card := by
  have hnodup' : (queue.tail ++ [page]).Nodup :=
    List.nodup_append.mpr ⟨hnodup.sublist (List.tail_sublist _), List.nodup_singleton _,
      by rintro a ha _ hb rfl; exact hpage (List.mem_singleton.mp hb ▸ List.mem_of_mem_tail ha)⟩
  have hlen : (queue.tail ++ [page]).length = queue.length := by
    cases queue <;> simp_all
  have hstep := rankPotential_fifo_step hnodup hne hpage cache
  have h1 := missingPotential_add_rankPotential hnodup cache
  have h2 := missingPotential_add_rankPotential hnodup' cache
  rw [hlen] at h2
  split_ifs at hstep ⊢ <;> omega

end PagingWithDelay.Analysis
