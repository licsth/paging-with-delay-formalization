import PagingWithDelay.Analysis.Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The rank potential

The write-up's potential for comparing a FIFO cache with an offline cache:

  `Φ = ∑_{q ∈ C_ALG ∩ C_OPT} rank q`,

where `rank` is the position in the FIFO queue, `1` for the page evicted next
and `k` for the page fetched last.  `rankPotential queue cache` is that sum for
a FIFO queue `queue` (a list, oldest page first) and an offline cache `cache`.

The lemmas are the write-up's "Potential changes":

* `rankPotential_le_triangular`: `0 ≤ Φ ≤ K = k(k+1)/2`, with equality when the
  caches coincide (`rankPotential_toFinset`);
* `rankPotential_fifo_step`: at a FIFO payment `Φ' = Φ - m + k·[p ∈ C_OPT]`,
  where `m = |C_ALG ∩ C_OPT|` before the payment;
* `rankPotential_le_of_sdiff_subset_singleton`: at an offline fetch that
  evicts at most one page `e`, `Φ ≥ Φ_before - rank e`, so `Φ` drops by at
  most `k`, and not at all when `e` is outside the FIFO queue.

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

theorem rankPotential_le_of_sdiff_eq_empty (queue : List α)
    {cache cache' : Finset α} (h : cache \ cache' = ∅) :
    rankPotential queue cache ≤ rankPotential queue cache' :=
  rankPotential_mono queue (Finset.sdiff_eq_empty_iff_subset.mp h)

/-! ### The maximal potential -/

omit [DecidableEq α] in
private theorem rank_cons_of_mem {head : α} {tail : List α} [DecidableEq α] {q : α}
    (hq : q ∈ tail) (hne : q ≠ head) : rank (head :: tail) q = rank tail q + 1 := by
  simp [rank, hq, List.idxOf_cons_ne _ (Ne.symm hne)]

omit [DecidableEq α] in
private theorem rank_cons_self (head : α) (tail : List α) [DecidableEq α] :
    rank (head :: tail) head = 1 := by
  simp [rank]

/-- Over the whole queue the ranks sum to `1 + ⋯ + k`. -/
theorem sum_rank_toFinset {queue : List α} (hnodup : queue.Nodup) :
    ∑ q ∈ queue.toFinset, rank queue q = triangular queue.length := by
  induction queue with
  | nil => simp [triangular]
  | cons head tail ih =>
      rw [List.nodup_cons] at hnodup
      have hcongr : ∀ q ∈ tail.toFinset, rank (head :: tail) q = rank tail q + 1 := by
        intro q hq
        have hqt : q ∈ tail := List.mem_toFinset.mp hq
        exact rank_cons_of_mem hqt (fun heq => hnodup.1 (by rw [← heq]; exact hqt))
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
      have hph : page ≠ head := fun h => hpage (h ▸ List.mem_cons_self ..)
      simp only [List.tail_cons]
      -- the new queue's shared pages: those of `tail`, plus `page` if the offline cache holds it
      have hnew : sharedPages (tail ++ [page]) cache =
          if page ∈ cache then insert page (sharedPages tail cache) else sharedPages tail cache := by
        unfold sharedPages
        rw [List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
          Finset.union_comm, ← Finset.insert_eq]
        split_ifs with h
        · rw [Finset.insert_inter_of_mem h]
        · rw [Finset.insert_inter_of_notMem h]
      have hold : sharedPages (head :: tail) cache =
          if head ∈ cache then insert head (sharedPages tail cache) else sharedPages tail cache := by
        unfold sharedPages
        rw [List.toFinset_cons]
        split_ifs with h
        · rw [Finset.insert_inter_of_mem h]
        · rw [Finset.insert_inter_of_notMem h]
      have hhead_not : head ∉ sharedPages tail cache :=
        fun h => hnodup.1 (List.mem_toFinset.mp (Finset.mem_inter.mp h).1)
      have hpage_not : page ∉ sharedPages tail cache :=
        fun h => hpt (List.mem_toFinset.mp (Finset.mem_inter.mp h).1)
      -- ranks in the new queue: unchanged for `tail`, `|queue|` for `page`
      have hrank_new : ∀ q ∈ sharedPages tail cache, rank (tail ++ [page]) q = rank tail q := by
        intro q hq
        have hqt : q ∈ tail := List.mem_toFinset.mp (Finset.mem_inter.mp hq).1
        simp [rank, hqt, List.idxOf_append_of_mem hqt]
      have hrank_old : ∀ q ∈ sharedPages tail cache, rank (head :: tail) q = rank tail q + 1 := by
        intro q hq
        have hqt : q ∈ tail := List.mem_toFinset.mp (Finset.mem_inter.mp hq).1
        exact rank_cons_of_mem hqt (fun heq => hnodup.1 (by rw [← heq]; exact hqt))
      have hrank_page : rank (tail ++ [page]) page = tail.length + 1 :=
        rank_append_self hpt
      have heta : (sharedPages tail cache).sum (rank tail) =
          ∑ x ∈ sharedPages tail cache, rank tail x := rfl
      unfold rankPotential
      rw [hnew, hold]
      simp only [List.length_cons]
      split_ifs with hp hh hh
      · rw [Finset.sum_insert hpage_not, Finset.sum_insert hhead_not, hrank_page,
          rank_cons_self, Finset.sum_congr rfl hrank_new, Finset.sum_congr rfl hrank_old,
          Finset.sum_add_distrib, Finset.sum_const, Finset.card_insert_of_notMem hhead_not]
        simp only [nsmul_eq_mul, Nat.cast_id, mul_one]
        omega
      · rw [Finset.sum_insert hpage_not, hrank_page, Finset.sum_congr rfl hrank_new,
          Finset.sum_congr rfl hrank_old, Finset.sum_add_distrib, Finset.sum_const]
        simp only [nsmul_eq_mul, Nat.cast_id, mul_one]
        omega
      · rw [Finset.sum_insert hhead_not, rank_cons_self, Finset.sum_congr rfl hrank_new,
          Finset.sum_congr rfl hrank_old, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_insert_of_notMem hhead_not]
        simp only [nsmul_eq_mul, Nat.cast_id, mul_one]
        omega
      · rw [Finset.sum_congr rfl hrank_new, Finset.sum_congr rfl hrank_old,
          Finset.sum_add_distrib, Finset.sum_const]
        simp only [nsmul_eq_mul, Nat.cast_id, mul_one]
        omega

end PagingWithDelay.Analysis
