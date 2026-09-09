import PagingWithDelay.KPlusOne.Setup
import PagingWithDelay.Competitive.DelayAccounting

/-!
# The FIFO cache as a window of payments

Under `Setup` the cache immediately before payment `i` is the list of the
pages fetched by payments `i - k, …, i - 1`; those pages are pairwise
distinct, so exactly one page of the `k+1`-page universe is missing from it.
That page is the one payment `i` fetches, and also the page evicted by payment
`i - 1`, fetched last at payment `i - k - 1`.
-/

namespace PagingWithDelay.KPlusOne

open PagingWithDelay

variable {Page : Type*} [DecidableEq Page]

namespace Setup

noncomputable section

variable (S : Setup Page)

/-- The FIFO cache immediately before payment `i`. -/
def queue (i : ℕ) : List Page := FIFO.recentPages S.cacheSize (S.payments.take i)

theorem take_length {i : ℕ} (hi : i ≤ S.count) : (S.payments.take i).length = i := by
  simpa [count] using Nat.min_eq_left hi

theorem queue_eq_drop {i : ℕ} (hi : i ≤ S.count) :
    S.queue i = (((S.payments.map FIFO.Payment.page).take i).drop (i - S.cacheSize)) := by
  unfold queue
  rw [FIFO.recentPages_eq_lastPaymentPages S.cacheSize S.positive]
  unfold FIFO.lastPaymentPages
  simp only [List.map_take, List.length_take, List.length_map]
  congr 2
  simp [count] at hi ⊢
  omega

theorem queue_length {i : ℕ} (hi : i ≤ S.count) :
    (S.queue i).length = min S.cacheSize i := by
  rw [queue_eq_drop S hi]
  simp only [List.length_drop, List.length_take, List.length_map]
  have : min i S.payments.length = i := Nat.min_eq_left hi
  rw [this]
  omega

theorem queue_getElem {i j : ℕ} (hi : i ≤ S.count) (hj : j < (S.queue i).length) :
    (S.queue i)[j] = S.pageAt (i - S.cacheSize + j) := by
  have hlen := queue_length S hi
  rw [hlen] at hj
  have hidx : i - S.cacheSize + j < S.count := by omega
  rw [pageAt_eq S hidx]
  have := queue_eq_drop S hi
  simp only [this, List.getElem_drop, List.getElem_take, List.getElem_map]

theorem exists_of_mem_queue {i : ℕ} (hi : i ≤ S.count) {x : Page} (hx : x ∈ S.queue i) :
    ∃ j, i - S.cacheSize ≤ j ∧ j < i ∧ S.pageAt j = x := by
  obtain ⟨j, hj, hgetElem⟩ := List.mem_iff_getElem.mp hx
  have hlen := queue_length S hi
  refine ⟨i - S.cacheSize + j, by omega, ?_, ?_⟩
  · rw [hlen] at hj; omega
  · rw [← queue_getElem S hi hj, hgetElem]

/-- Two payments fetching the same page are more than `k` apart. -/
theorem payment_spacing {i j : ℕ} (hj : j < S.count) (hij : i < j)
    (hpage : S.pageAt i = S.pageAt j) : i + S.cacheSize < j := by
  have hi : i < S.count := hij.trans hj
  rw [pageAt_eq S hi, pageAt_eq S hj] at hpage
  have := FIFO.samePage_spacing (δ := S.threshold) S.input S.valid
    (i := i) (j := j) (by simpa [count, payments] using hi) (by simpa [count, payments] using hj)
    hij (by simpa [payments] using hpage)
  rw [S.size] at this
  exact this

theorem queue_nodup {i : ℕ} (hi : i ≤ S.count) : (S.queue i).Nodup := by
  have hlen := queue_length S hi
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro a b ha hb hab heq
  rw [queue_getElem S hi ha, queue_getElem S hi hb] at heq
  rw [hlen] at ha hb
  have := payment_spacing S (i := i - S.cacheSize + a) (j := i - S.cacheSize + b)
    (by omega) (by omega) heq
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

theorem queue_subset_pages {i : ℕ} (hi : i ≤ S.count) {x : Page} (hx : x ∈ S.queue i) :
    x ∈ S.pages := by
  obtain ⟨j, _, hj, rfl⟩ := exists_of_mem_queue S hi hx
  exact pageAt_mem_pages S (lt_of_lt_of_le hj hi)

/-- Freshness: a payment fetches a page that is not in the cache. -/
theorem pageAt_not_mem_queue {i : ℕ} (hi : i < S.count) : S.pageAt i ∉ S.queue i := by
  rw [pageAt_eq S hi]
  have h := (FIFO.final_freshPayments (δ := S.threshold) S.input S.valid).fresh_at i
    (by simpa [count] using hi)
  rw [S.size] at h
  exact h

/-- With `k + 1` pages and a full cache, the page fetched by payment `i` is
the *only* page missing from the cache. -/
theorem eq_pageAt_of_not_mem_queue {i : ℕ} (hfull : S.cacheSize ≤ i) (hi : i < S.count)
    {x : Page} (hx : x ∈ S.pages) (hnot : x ∉ S.queue i) : x = S.pageAt i := by
  classical
  set Q := (S.queue i).toFinset with hQ
  have hcardQ : Q.card = S.cacheSize := by
    rw [hQ, List.toFinset_card_of_nodup (queue_nodup S (le_of_lt hi)),
      queue_length S (le_of_lt hi)]
    omega
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
  exact (FIFO.recentPages_append S.cacheSize (S.payments.take i)
    (FIFO.recentPages S.cacheSize (S.payments.take i)) S.payments[i] rfl).symm

theorem queue_succ_full {i : ℕ} (hfull : S.cacheSize ≤ i) (hi : i < S.count) :
    S.queue (i + 1) = (S.queue i).tail ++ [S.pageAt i] := by
  rw [queue_succ S hi, FIFO.insertPage]
  have hlen : (S.queue i).length = S.cacheSize := by
    rw [queue_length S (le_of_lt hi)]; omega
  rw [if_neg (by omega)]

/-- The page fetched by payment `i` was last fetched by payment `i - k - 1`. -/
theorem pageAt_previous {i : ℕ} (hfull : S.cacheSize + 1 ≤ i) (hi : i < S.count) :
    S.pageAt (i - S.cacheSize - 1) = S.pageAt i := by
  refine eq_pageAt_of_not_mem_queue S (by omega) hi
    (pageAt_mem_pages S (by omega)) ?_
  intro hmem
  obtain ⟨j, hlow, hhigh, heq⟩ := exists_of_mem_queue S (le_of_lt hi) hmem
  have hlt : i - S.cacheSize - 1 < j := by omega
  have := payment_spacing S (i := i - S.cacheSize - 1) (j := j) (by omega) hlt heq.symm
  omega

/-- Every request served by payment `i` arrived after payment `i - 1`, which
is when the fetched page was evicted. -/
theorem served_arrival_gt {i : ℕ} (hfull : S.cacheSize + 1 ≤ i) (hi : i < S.count)
    {occurrence : Occurrence Page} (ho : occurrence ∈ (S.payments[i]).served) :
    S.timeAt (i - 1) < occurrence.request.arrival := by
  have hprevious : i - S.cacheSize - 1 < i := by omega
  have hlt : i - S.cacheSize - 1 < S.count := by omega
  have hlen : i - S.cacheSize - 1 < S.payments.length := by simpa [count] using hlt
  have hsame : (S.payments[i - S.cacheSize - 1]'hlen).page = (S.payments[i]).page := by
    rw [← pageAt_eq S hlt, ← pageAt_eq S hi]
    exact pageAt_previous S hfull hi
  have hbound := FIFO.History.final_validBatchLowerBounds (δ := S.threshold) S.input S.valid
    i (by simpa [count, payments] using hi) occurrence (by simpa [payments] using ho)
    (i - S.cacheSize - 1) hprevious (by simpa [payments] using hsame)
  have hidx : i - S.cacheSize - 1 + S.input.cacheSize = i - 1 := by
    rw [S.size]; omega
  rw [hidx] at hbound
  have hlt : i - 1 < S.count := by omega
  have := hbound.2
  rw [show (FIFO.run S.threshold S.input (2 * S.input.requests.length)
      (FIFO.initialState S.input)).payments = S.payments from rfl] at this
  rw [List.getElem?_eq_getElem (by simpa [count] using hlt)] at this
  rw [timeAt_eq S hlt]
  simpa using this

end

end Setup

end PagingWithDelay.KPlusOne
