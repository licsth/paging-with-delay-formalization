import PagingWithDelay.KPlusOne.Setup
import PagingWithDelay.Competitive.DelayAccounting

/-!
# The FIFO cache as a window of the eviction order

Under `Setup` the cache immediately before payment `i` is the window of `k`
consecutive entries `i, …, i + k - 1` of the *eviction order* — the initial
cache followed by the fetched pages, whose entry `j` is the page payment `j`
evicts.  Those entries are pairwise distinct, so exactly one page of the
`k+1`-page universe is missing from the cache.  That page is the one payment
`i` fetches, and also the entry `i - 1` of the eviction order: the page evicted
by payment `i - 1`, or for `i = 0` the one page outside the initial cache.
-/

namespace PagingWithDelay.KPlusOne

open PagingWithDelay

variable {Page : Type*} [DecidableEq Page]

namespace Setup

noncomputable section

variable (S : Setup Page)

/-! ### The eviction order -/

/-- The initial cache followed by the fetched pages; entry `j` is the page
payment `j` evicts. -/
def seqList : List Page := FIFO.History.evictionOrder S.input S.payments

theorem seqList_length : S.seqList.length = S.cacheSize + S.count := by
  simp [seqList, count, S.initialCache_length]

/-- `seqList` read as a total function. -/
def seq (j : ℕ) : Page := (S.seqList[j]?).getD S.somePage

theorem seq_eq {j : ℕ} (hj : j < S.cacheSize + S.count) :
    S.seq j = S.seqList[j]'(by rw [seqList_length]; exact hj) := by
  unfold seq
  rw [List.getElem?_eq_getElem]
  rfl

theorem seq_initial {p : ℕ} (hp : p < S.cacheSize) :
    S.seq p = S.input.initialCache[p]'(by rw [S.initialCache_length]; exact hp) := by
  unfold seq seqList FIFO.History.evictionOrder
  rw [List.getElem?_append_left (by rw [S.initialCache_length]; exact hp),
    List.getElem?_eq_getElem]
  rfl

/-- Payment `i` fetches entry `k + i` of the eviction order (as total
functions, so no bound on `i` is needed). -/
theorem pageAt_eq_seq (i : ℕ) : S.pageAt i = S.seq (S.cacheSize + i) := by
  unfold seq seqList FIFO.History.evictionOrder pageAt
  rw [List.getElem?_append_right (by rw [S.initialCache_length]; omega), S.initialCache_length,
    Nat.add_sub_cancel_left, List.getElem?_map]

/-! ### The cache before a payment -/

/-- The FIFO cache immediately before payment `i`. -/
def queue (i : ℕ) : List Page :=
  FIFO.recentPages S.cacheSize S.input.initialCache (S.payments.take i)

theorem take_length {i : ℕ} (hi : i ≤ S.count) : (S.payments.take i).length = i := by
  simpa [count] using Nat.min_eq_left hi

theorem queue_eq_drop {i : ℕ} (hi : i ≤ S.count) :
    S.queue i = (S.seqList.take (S.cacheSize + i)).drop i := by
  unfold queue
  rw [FIFO.recentPages_eq_lastPaymentPages S.cacheSize S.positive S.input.initialCache
    S.initialCache_length.le]
  unfold FIFO.lastPaymentPages seqList FIFO.History.evictionOrder
  rw [← S.initialCache_length, List.take_length_add_append, ← List.map_take]
  simp only [List.length_append, List.length_map, take_length S hi]
  congr 1
  omega

theorem queue_length {i : ℕ} (hi : i ≤ S.count) : (S.queue i).length = S.cacheSize := by
  rw [queue_eq_drop S hi]
  simp only [List.length_drop, List.length_take, seqList_length]
  omega

theorem queue_getElem {i j : ℕ} (hi : i ≤ S.count) (hj : j < (S.queue i).length) :
    (S.queue i)[j] = S.seq (i + j) := by
  have hlen := queue_length S hi
  rw [hlen] at hj
  rw [seq_eq S (by omega)]
  simp only [queue_eq_drop S hi, List.getElem_drop, List.getElem_take]

theorem exists_of_mem_queue {i : ℕ} (hi : i ≤ S.count) {x : Page} (hx : x ∈ S.queue i) :
    ∃ j, i ≤ j ∧ j < i + S.cacheSize ∧ S.seq j = x := by
  obtain ⟨j, hj, hgetElem⟩ := List.mem_iff_getElem.mp hx
  have hlen := queue_length S hi
  refine ⟨i + j, by omega, ?_, ?_⟩
  · rw [hlen] at hj; omega
  · rw [← queue_getElem S hi hj, hgetElem]

/-- Freshness: a payment fetches a page that is not in the cache. -/
theorem pageAt_not_mem_queue {i : ℕ} (hi : i < S.count) : S.pageAt i ∉ S.queue i := by
  rw [pageAt_eq S hi]
  have h := (FIFO.final_freshPayments (δ := S.threshold) S.input S.valid).fresh_at i
    (by simpa [count] using hi)
  rw [S.size] at h
  exact h

/-- Two entries of the eviction order holding the same page are more than `k`
apart: the later one was fetched into a cache from which the page was absent,
and that cache is the window of the `k` entries before it. -/
theorem seq_spacing {i j : ℕ} (hj : j < S.cacheSize + S.count) (hij : i < j)
    (hpage : S.seq i = S.seq j) : i + S.cacheSize < j := by
  by_cases hjk : j < S.cacheSize
  · exfalso
    rw [seq_initial S hjk, seq_initial S (by omega)] at hpage
    have hnodup := S.valid.initialCache_nodup
    have := (List.Nodup.getElem_inj_iff hnodup).mp hpage
    omega
  · have hm : j - S.cacheSize < S.count := by omega
    by_contra hnot
    push_neg at hnot
    apply pageAt_not_mem_queue S hm
    rw [pageAt_eq_seq S _, show S.cacheSize + (j - S.cacheSize) = j by omega, ← hpage]
    have hidx : i - (j - S.cacheSize) < (S.queue (j - S.cacheSize)).length := by
      rw [queue_length S hm.le]; omega
    rw [show i = j - S.cacheSize + (i - (j - S.cacheSize)) by omega,
      ← queue_getElem S hm.le hidx]
    exact List.getElem_mem hidx

/-- Two payments fetching the same page are more than `k` apart. -/
theorem payment_spacing {i j : ℕ} (hj : j < S.count) (hij : i < j)
    (hpage : S.pageAt i = S.pageAt j) : i + S.cacheSize < j := by
  rw [pageAt_eq_seq, pageAt_eq_seq] at hpage
  have := seq_spacing S (i := S.cacheSize + i) (j := S.cacheSize + j) (by omega) (by omega) hpage
  omega

theorem queue_nodup {i : ℕ} (hi : i ≤ S.count) : (S.queue i).Nodup := by
  have hlen := queue_length S hi
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro a b ha hb hab heq
  rw [queue_getElem S hi ha, queue_getElem S hi hb] at heq
  rw [hlen] at ha hb
  have := seq_spacing S (i := i + a) (j := i + b) (by omega) (by omega) heq
  omega

/-! ### Payment pages belong to the universe -/

theorem payment_delayCost {i : ℕ} (hi : i < S.count) :
    (S.payments[i]).delayCost = S.threshold :=
  FIFO.final_thresholdPayments S.input _ (List.getElem_mem (by simpa [count] using hi))

theorem served_ne_nil {i : ℕ} (hi : i < S.count) : (S.payments[i]).served ≠ [] := by
  intro hempty
  have hcost := payment_delayCost S hi
  rw [FIFO.Payment.delayCost, hempty] at hcost
  simp only [List.map_nil, List.sum_nil] at hcost
  exact absurd hcost.symm (ne_of_gt S.threshold_pos)

theorem served_authentic {i : ℕ} (hi : i < S.count) {occurrence : Occurrence Page}
    (ho : occurrence ∈ (S.payments[i]).served) :
    occurrence ∈ enumerate S.input.requests :=
  (FIFO.History.final_authentic (δ := S.threshold) S.input).2.2 _
    (List.getElem_mem (by simpa [count] using hi)) occurrence ho

theorem served_request_mem {i : ℕ} (hi : i < S.count) {occurrence : Occurrence Page}
    (ho : occurrence ∈ (S.payments[i]).served) :
    occurrence.request ∈ S.input.requests := by
  rw [← FIFO.enumerate_map_request S.input.requests]
  exact List.mem_map_of_mem (served_authentic S hi ho)

theorem served_page {i : ℕ} (hi : i < S.count) {occurrence : Occurrence Page}
    (ho : occurrence ∈ (S.payments[i]).served) :
    occurrence.request.page = S.pageAt i := by
  rw [pageAt_eq S hi]
  exact (FIFO.History.final_validBatches S.input S.valid _
    (List.getElem_mem (by simpa [count] using hi)) occurrence ho).1

theorem served_arrival_le {i : ℕ} (hi : i < S.count) {occurrence : Occurrence Page}
    (ho : occurrence ∈ (S.payments[i]).served) :
    occurrence.request.arrival ≤ S.timeAt i := by
  rw [timeAt_eq S hi]
  exact (FIFO.History.final_validBatches S.input S.valid _
    (List.getElem_mem (by simpa [count] using hi)) occurrence ho).2

theorem pageAt_mem_pages {i : ℕ} (hi : i < S.count) : S.pageAt i ∈ S.pages := by
  obtain ⟨occurrence, ho⟩ := List.exists_mem_of_ne_nil _ (served_ne_nil S hi)
  rw [← served_page S hi ho]
  exact S.requestPages _ (served_request_mem S hi ho)

theorem seq_mem_pages {j : ℕ} (hj : j < S.cacheSize + S.count) : S.seq j ∈ S.pages := by
  by_cases hjk : j < S.cacheSize
  · rw [seq_initial S hjk]
    exact S.initialPages _ (List.getElem_mem _)
  · rw [show j = S.cacheSize + (j - S.cacheSize) by omega, ← pageAt_eq_seq]
    exact pageAt_mem_pages S (by omega)

theorem queue_subset_pages {i : ℕ} (hi : i ≤ S.count) {x : Page} (hx : x ∈ S.queue i) :
    x ∈ S.pages := by
  obtain ⟨j, _, hj, rfl⟩ := exists_of_mem_queue S hi hx
  exact seq_mem_pages S (by omega)

/-- With `k + 1` pages and a full cache, the page fetched by payment `i` is
the *only* page missing from the cache. -/
theorem eq_pageAt_of_not_mem_queue {i : ℕ} (hi : i < S.count)
    {x : Page} (hx : x ∈ S.pages) (hnot : x ∉ S.queue i) : x = S.pageAt i := by
  classical
  set Q := (S.queue i).toFinset with hQ
  have hcardQ : Q.card = S.cacheSize := by
    rw [hQ, List.toFinset_card_of_nodup (queue_nodup S (le_of_lt hi)),
      queue_length S (le_of_lt hi)]
  have hsubset : Q ⊆ S.pages := by
    intro y hy
    exact queue_subset_pages S (le_of_lt hi) (List.mem_toFinset.mp hy)
  have hcarddiff : (S.pages \ Q).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsubset, S.card, hcardQ]
    omega
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcarddiff
  have hxmem : x ∈ S.pages \ Q := by
    refine Finset.mem_sdiff.mpr ⟨hx, ?_⟩
    rw [hQ, List.mem_toFinset]
    exact hnot
  have hpmem : S.pageAt i ∈ S.pages \ Q := by
    refine Finset.mem_sdiff.mpr ⟨pageAt_mem_pages S hi, ?_⟩
    rw [hQ, List.mem_toFinset]
    exact pageAt_not_mem_queue S hi
  rw [hy] at hxmem hpmem
  rw [Finset.mem_singleton] at hxmem hpmem
  rw [hxmem, hpmem]

/-! ### The FIFO replacement step -/

theorem queue_succ {i : ℕ} (hi : i < S.count) :
    S.queue (i + 1) = FIFO.insertPage S.cacheSize (S.queue i) (S.pageAt i) := by
  unfold queue
  rw [pageAt_eq S hi]
  have htake : S.payments.take (i + 1) = S.payments.take i ++ [S.payments[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simpa [count] using hi)]
    rfl
  rw [htake]
  exact (FIFO.recentPages_append S.cacheSize S.input.initialCache (S.payments.take i)
    (FIFO.recentPages S.cacheSize S.input.initialCache (S.payments.take i))
    S.payments[i] rfl).symm

/-- The cache is always full, so every payment evicts the front of the queue. -/
theorem queue_succ_full {i : ℕ} (hi : i < S.count) :
    S.queue (i + 1) = (S.queue i).tail ++ [S.pageAt i] := by
  rw [queue_succ S hi, FIFO.insertPage]
  have hlen : (S.queue i).length = S.cacheSize := queue_length S (le_of_lt hi)
  rw [if_neg (by omega)]

/-- The page fetched by payment `i` is entry `i - 1` of the eviction order: the
page evicted by payment `i - 1`, or for `i = 0` the page outside the initial
cache.  (For `i = 0` the entry is `seq 0`, the front of the initial queue,
which is *not* the fetched page; the statement is therefore restricted to
`1 ≤ i`.) -/
theorem seq_pred_eq_pageAt {i : ℕ} (hi1 : 1 ≤ i) (hi : i < S.count) :
    S.seq (i - 1) = S.pageAt i := by
  refine eq_pageAt_of_not_mem_queue S hi (seq_mem_pages S (by omega)) ?_
  intro hmem
  obtain ⟨j, hlow, hhigh, heq⟩ := exists_of_mem_queue S (le_of_lt hi) hmem
  have := seq_spacing S (i := i - 1) (j := j) (by omega) (by omega) heq.symm
  omega

/-- Every request served by payment `i ≥ 1` arrived after payment `i - 1`,
which is when the fetched page was evicted. -/
theorem served_arrival_gt {i : ℕ} (hi1 : 1 ≤ i) (hi : i < S.count)
    {occurrence : Occurrence Page} (ho : occurrence ∈ (S.payments[i]).served) :
    S.timeAt (i - 1) < occurrence.request.arrival := by
  have hlen : i < S.payments.length := by simpa [count] using hi
  have hprev : i - 1 < S.count := by omega
  have hsame : S.seq (i - 1) = S.payments[i].page := by
    rw [seq_pred_eq_pageAt S hi1 hi, pageAt_eq S hi]
  have hbound : (S.payments[i - 1]?).any
      (fun payment => payment.time < occurrence.request.arrival) := by
    by_cases hk : i - 1 < S.cacheSize
    · rw [seq_initial S hk] at hsame
      exact (FIFO.History.final_validBatchLowerBounds_initial (δ := S.threshold) S.input
        S.valid i hlen occurrence ho (i - 1) (by rw [S.initialCache_length]; exact hk)
        hsame).2
    · have hp : i - 1 - S.cacheSize < S.count := by omega
      rw [show i - 1 = S.cacheSize + (i - 1 - S.cacheSize) by omega, ← pageAt_eq_seq,
        pageAt_eq S hp] at hsame
      have := (FIFO.History.final_validBatchLowerBounds_payment (δ := S.threshold) S.input
        S.valid i hlen occurrence ho (i - 1 - S.cacheSize) (by omega) hsame).2
      rw [S.size, show i - 1 - S.cacheSize + S.cacheSize = i - 1 by omega] at this
      exact this
  rw [List.getElem?_eq_getElem (by simpa [count] using hprev)] at hbound
  rw [timeAt_eq S hprev]
  simpa using hbound

end

end Setup

end PagingWithDelay.KPlusOne
