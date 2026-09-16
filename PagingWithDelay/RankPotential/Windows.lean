import PagingWithDelay.RankPotential.Setup

/-!
# Payment windows

The write-up's payment window `W_i` ends at payment `i` and starts at time `0`
if `pageAt i` has never been evicted, otherwise immediately after FIFO's last
eviction of `pageAt i` before payment `i`.  In the eviction order, the
evictions of `pageAt i` before payment `i` are the entries `j < k + i` holding
that page — entry `k + i` being payment `i`'s own fetch — and each such entry
is a payment `j < i`.  `lastEviction i` is the last of them.

The lemma "Properties of payment windows" becomes:

* `pageAt_not_mem_queue_of_window`: `pageAt i` is outside the FIFO cache
  before every payment `m` in the window (after the last eviction, up to `i`);
* `served_arrival_gt_lastEviction` / `served_arrival_le`: every request served
  at payment `i` arrives inside `W_i`;
* `payment_delayCost`: those requests have accumulated exactly `δ`;
* `lastEviction_ge_of_same_page`: for two payments of the same page the later
  window starts after the earlier payment, so windows of one page are disjoint.
-/

namespace PagingWithDelay.RankPotential

open PagingWithDelay

variable {Page : Type*} [DecidableEq Page]

namespace Setup

noncomputable section

variable (S : Setup Page)

/-- The evictions of `pageAt i` before payment `i`, as entries of the
eviction order. -/
def evictions (i : ℕ) : Finset ℕ :=
  (Finset.range (S.cacheSize + i)).filter fun j => S.seq j = S.pageAt i

theorem mem_evictions {i j : ℕ} :
    j ∈ S.evictions i ↔ j < S.cacheSize + i ∧ S.seq j = S.pageAt i := by
  simp [evictions]

/-- Every eviction of `pageAt i` before payment `i` is a payment `j < i`. -/
theorem lt_of_mem_evictions {i j : ℕ} (hi : i < S.count) (hj : j ∈ S.evictions i) : j < i := by
  rw [mem_evictions] at hj
  have := seq_spacing S (i := j) (j := S.cacheSize + i) (by omega) hj.1 hj.2
  omega

/-- The last eviction of `pageAt i` before payment `i`, if any. -/
def lastEviction (i : ℕ) : Option ℕ :=
  if h : (S.evictions i).Nonempty then some ((S.evictions i).max' h) else none

theorem lastEviction_mem {i j : ℕ} (h : S.lastEviction i = some j) : j ∈ S.evictions i := by
  unfold lastEviction at h
  split at h
  · rename_i hne
    rw [Option.some_inj] at h
    rw [← h]
    exact Finset.max'_mem _ hne
  · simp at h

theorem le_lastEviction {i j j' : ℕ} (h : S.lastEviction i = some j) (hj' : j' ∈ S.evictions i) :
    j' ≤ j := by
  unfold lastEviction at h
  split at h
  · rw [Option.some_inj] at h
    rw [← h]
    exact Finset.le_max' _ _ hj'
  · simp at h

theorem lastEviction_none {i : ℕ} (h : S.lastEviction i = none) : S.evictions i = ∅ := by
  unfold lastEviction at h
  split at h
  · simp at h
  · rename_i hne
    exact Finset.not_nonempty_iff_eq_empty.mp hne

theorem lastEviction_lt {i j : ℕ} (hi : i < S.count) (h : S.lastEviction i = some j) : j < i :=
  lt_of_mem_evictions S hi (lastEviction_mem S h)

/-- **Windows, first property.**  `pageAt i` is outside the FIFO cache before
every payment `m` of its window: after the last eviction (if any) and up to
payment `i` itself. -/
theorem pageAt_not_mem_queue_of_window {i m : ℕ} (hi : i < S.count) (hm : m ≤ i)
    (hlast : ∀ j, S.lastEviction i = some j → j < m) :
    S.pageAt i ∉ S.queue m := by
  intro hmem
  obtain ⟨l, hlow, hhigh, hl⟩ := exists_of_mem_queue S (hm.trans hi.le) hmem
  by_cases hli : l < S.cacheSize + i
  · have hlmem : l ∈ S.evictions i := (mem_evictions S).mpr ⟨hli, hl⟩
    cases hle : S.lastEviction i with
    | none => simp [lastEviction_none S hle] at hlmem
    | some j =>
        have := le_lastEviction S hle hlmem
        have := hlast j hle
        omega
  · omega

/-- **Windows, first property, arrivals.**  A request served at payment `i`
arrives strictly after the last eviction of its page. -/
theorem served_arrival_gt_lastEviction {i j : ℕ} (hi : i < S.count)
    (h : S.lastEviction i = some j) {occurrence : Occurrence Page}
    (ho : occurrence ∈ (S.payments[i]).served) :
    S.timeAt j < occurrence.request.arrival := by
  have hj := (mem_evictions S).mp (lastEviction_mem S h)
  exact (served_arrival_gt S hi hj.1 hj.2 ho).2

/-- **Windows, third property.**  If payments `i < i'` fetch the same page,
the window of `i'` starts after payment `i` — indeed after payment `k + i`,
the one that evicted that page again — so windows of one page are disjoint. -/
theorem lastEviction_ge_of_same_page {i i' : ℕ} (hi' : i' < S.count) (hii' : i < i')
    (hpage : S.pageAt i = S.pageAt i') :
    ∃ j, S.lastEviction i' = some j ∧ S.cacheSize + i ≤ j := by
  have hmem : S.cacheSize + i ∈ S.evictions i' := by
    rw [mem_evictions]
    have := payment_spacing S hi' hii' hpage
    exact ⟨by omega, hpage⟩
  unfold lastEviction
  rw [dif_pos ⟨_, hmem⟩]
  exact ⟨_, rfl, Finset.le_max' _ _ hmem⟩

end

end Setup

end PagingWithDelay.RankPotential
