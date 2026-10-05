import Algorithm
import Proofs.EventLoop.FreshQueue
import Proofs.EventLoop.History
import Proofs.EventLoop.PaymentAccounting
import Proofs.EventLoop.PaymentOrder
import Proofs.EventLoop.TemporalInvariant
import Proofs.Competitive.CostDefs

/-!
# The FIFO run read through its eviction order

The common ground of the write-up's two upper bounds: a instance, a
positive threshold `δ`, and the completed run of `δ`-FIFO on it.  This file
names the run's payments `0, …, M-1` with their pages `pageAt i` and times
`timeAt i`, and describes the FIFO cache before payment `i` as the window of
`k` consecutive entries `i, …, i + k - 1` of the *eviction order* `seq` — the
initial cache followed by the fetched pages, whose entry `j` is the page
payment `j` evicts.

Everything is read off the event loop of `Algorithm.lean` through the
threshold-independent invariants in `EventLoop/`.  Nothing here mentions a
comparator.
-/

namespace PagingWithDelay.RankPotential

open PagingWithDelay

variable {Page : Type*} [DecidableEq Page]

/-- A instance with a positive threshold. -/
structure Setup (Page : Type*) [DecidableEq Page] where
  /-- The cache size `k`. -/
  cacheSize : ℕ
  positive : 0 < cacheSize
  /-- The threshold `δ`. -/
  threshold : Cost
  threshold_pos : 0 < threshold
  input : Instance Page
  size : input.cacheSize = cacheSize

namespace Setup

noncomputable section

variable (S : Setup Page)

theorem initialCache_length : S.input.initialCache.length = S.cacheSize := by
  rw [S.input.initialCache_full, S.size]

/-- The completed FIFO run at threshold `δ`. -/
def payments : List (FIFO.Payment Page) :=
  (FIFO.run S.threshold S.input (2 * S.input.requests.length)
    (FIFO.initialState S.input)).payments

/-- `M`, the number of payments. -/
def count : ℕ := S.payments.length

theorem count_eq_paymentCount : S.count = FIFO.paymentCount S.threshold S.input := rfl

/-! ### The eviction order -/

/-- The initial cache followed by the fetched pages; entry `j` is the page
payment `j` evicts. -/
def seqList : List Page := FIFO.History.evictionOrder S.input S.payments

theorem seqList_length : S.seqList.length = S.cacheSize + S.count := by
  simp [seqList, count, S.initialCache_length]

/-- A junk page used only as the default of the total functions below; it
exists as soon as the cache is nonempty. -/
def somePage : Page := S.input.initialCache.head (by
  intro h
  have := S.initialCache_length
  rw [h] at this
  simp at this
  exact absurd this.symm (Nat.pos_iff_ne_zero.mp S.positive))

/-- `seqList` read as a total function. -/
def seq (j : ℕ) : Page := (S.seqList[j]?).getD S.somePage

/-- The page fetched by payment `i`: entry `k + i` of the eviction order. -/
def pageAt (i : ℕ) : Page := S.seq (S.cacheSize + i)

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

theorem pageAt_eq {i : ℕ} (hi : i < S.count) : S.pageAt i = S.payments[i].page := by
  unfold pageAt seq seqList FIFO.History.evictionOrder
  rw [List.getElem?_append_right (by rw [S.initialCache_length]; omega), S.initialCache_length,
    Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_eq_getElem (by simpa [count] using hi)]
  rfl

/-! ### Payment times -/

/-- The time of payment `i`, clamped at the last payment so that it is
monotone as a function on all of `ℕ`. -/
def timeAt (i : ℕ) : Time :=
  ((S.payments[min i (S.count - 1)]?).map FIFO.Payment.time).getD 0

theorem timeAt_eq {i : ℕ} (hi : i < S.count) : S.timeAt i = S.payments[i].time := by
  unfold timeAt
  rw [min_eq_left (by omega), List.getElem?_eq_getElem hi]
  rfl

theorem payment_time_le {i j : ℕ} (hi : i < S.count) (hj : j < S.count) (hij : i ≤ j) :
    S.payments[i].time ≤ S.payments[j].time := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact List.pairwise_iff_getElem.mp
      (FIFO.final_payment_times_chronological (δ := S.threshold) S.input) i j hi hj hlt

theorem timeAt_mono : Monotone S.timeAt := by
  intro i j hij
  unfold timeAt
  rcases Nat.eq_zero_or_pos S.count with hzero | hpos
  · have : S.payments = [] := List.eq_nil_of_length_eq_zero hzero
    simp [this]
  · have hi : min i (S.count - 1) < S.count := by omega
    have hj : min j (S.count - 1) < S.count := by omega
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    simpa using S.payment_time_le hi hj (by omega)

/-! ### The cache before a payment -/

/-- The FIFO cache immediately before payment `i`. -/
def queue (i : ℕ) : List Page :=
  FIFO.recentPages S.cacheSize S.input.initialCache (S.payments.take i)

theorem take_length {i : ℕ} (hi : i ≤ S.count) : (S.payments.take i).length = i := by
  simpa [count] using Nat.min_eq_left hi

theorem queue_zero : S.queue 0 = S.input.initialCache := by
  simp [queue, FIFO.recentPages]

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

/-- The cache is always full. -/
theorem queue_length {i : ℕ} (hi : i ≤ S.count) : (S.queue i).length = S.cacheSize := by
  rw [queue_eq_drop S hi]
  simp only [List.length_drop, List.length_take, seqList_length]
  omega

theorem queue_ne_nil {i : ℕ} (hi : i ≤ S.count) : S.queue i ≠ [] := by
  intro h
  have := queue_length S hi
  rw [h] at this
  simp at this
  exact absurd this.symm (Nat.pos_iff_ne_zero.mp S.positive)

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

theorem seq_mem_queue {i j : ℕ} (hi : i ≤ S.count) (hlow : i ≤ j) (hhigh : j < i + S.cacheSize) :
    S.seq j ∈ S.queue i := by
  have hidx : j - i < (S.queue i).length := by rw [queue_length S hi]; omega
  rw [show j = i + (j - i) by omega, ← queue_getElem S hi hidx]
  exact List.getElem_mem hidx

/-- Freshness: a payment fetches a page that is not in the cache. -/
theorem pageAt_not_mem_queue {i : ℕ} (hi : i < S.count) : S.pageAt i ∉ S.queue i := by
  rw [pageAt_eq S hi]
  have h := (FIFO.final_freshPayments (δ := S.threshold) S.input).fresh_at i
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
    have hnodup := S.input.initialCache_nodup
    have := (List.Nodup.getElem_inj_iff hnodup).mp hpage
    omega
  · have hm : j - S.cacheSize < S.count := by omega
    by_contra hnot
    push_neg at hnot
    apply pageAt_not_mem_queue S hm
    rw [pageAt, show S.cacheSize + (j - S.cacheSize) = j by omega, ← hpage]
    exact seq_mem_queue S hm.le (by omega) (by omega)

/-- Two payments fetching the same page are more than `k` apart. -/
theorem payment_spacing {i j : ℕ} (hj : j < S.count) (hij : i < j)
    (hpage : S.pageAt i = S.pageAt j) : i + S.cacheSize < j := by
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

/-- Every payment evicts the front of the queue and appends the fetched page. -/
theorem queue_succ_full {i : ℕ} (hi : i < S.count) :
    S.queue (i + 1) = (S.queue i).tail ++ [S.pageAt i] := by
  rw [queue_succ S hi, FIFO.insertPage]
  have hlen : (S.queue i).length = S.cacheSize := queue_length S (le_of_lt hi)
  rw [if_neg (by omega)]

/-! ### The requests a payment serves -/

/-- The threshold rule: the requests served at a payment have accumulated
exactly `δ`. -/
theorem payment_delayCost {i : ℕ} (hi : i < S.count) :
    (S.payments[i]).delayCost = S.threshold :=
  FIFO.final_thresholdPayments S.input _ (List.getElem_mem (by simpa [count] using hi))

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
  exact (FIFO.History.final_validBatches S.input _
    (List.getElem_mem (by simpa [count] using hi)) occurrence ho).1

theorem served_arrival_le {i : ℕ} (hi : i < S.count) {occurrence : Occurrence Page}
    (ho : occurrence ∈ (S.payments[i]).served) :
    occurrence.request.arrival ≤ S.timeAt i := by
  rw [timeAt_eq S hi]
  exact (FIFO.History.final_validBatches S.input _
    (List.getElem_mem (by simpa [count] using hi)) occurrence ho).2

/-- The lower end of the payment window: a request served by payment `i`
arrived strictly after every payment `j` that evicted its page, that is,
after every earlier entry `j` of the eviction order holding `pageAt i`. -/
theorem served_arrival_gt {i j : ℕ} (hi : i < S.count) (hj : j < S.cacheSize + i)
    (hpage : S.seq j = S.pageAt i) {occurrence : Occurrence Page}
    (ho : occurrence ∈ (S.payments[i]).served) :
    j < i ∧ S.timeAt j < occurrence.request.arrival := by
  have hlen : i < S.payments.length := by simpa [count] using hi
  have hseq : (FIFO.History.evictionOrder S.input S.payments)[j]'(by
      simp [S.initialCache_length]; omega) = S.payments[i].page := by
    rw [← pageAt_eq S hi, ← hpage, seq_eq S (by omega)]
    rfl
  obtain ⟨hlt, hbound⟩ := FIFO.History.final_validBatchLowerBounds (δ := S.threshold) S.input
    i hlen occurrence ho j (by rw [S.initialCache_length]; exact hj) hseq
  refine ⟨hlt, ?_⟩
  rw [List.getElem?_eq_getElem (by simpa [count] using hlt.trans hi)] at hbound
  rw [timeAt_eq S (hlt.trans hi)]
  simpa using hbound

/-- With a positive threshold every payment serves at least one request. -/
theorem served_ne_nil {i : ℕ} (hi : i < S.count) : (S.payments[i]).served ≠ [] := by
  intro hempty
  have hcost := payment_delayCost S hi
  rw [FIFO.Payment.delayCost, hempty] at hcost
  simp only [List.map_nil, List.sum_nil] at hcost
  exact absurd hcost.symm (ne_of_gt S.threshold_pos)

/-! ### The page universe -/

/-- Every fetched page was requested, hence lies in the page universe. -/
theorem pageAt_mem_pageUniverse {i : ℕ} (hi : i < S.count) :
    S.pageAt i ∈ S.input.pageUniverse := by
  obtain ⟨occurrence, ho⟩ := List.exists_mem_of_ne_nil _ (served_ne_nil S hi)
  rw [← served_page S hi ho, Instance.pageUniverse, List.mem_toFinset, List.mem_append]
  exact Or.inr (List.mem_map_of_mem (served_request_mem S hi ho))

theorem seq_mem_pageUniverse {j : ℕ} (hj : j < S.cacheSize + S.count) :
    S.seq j ∈ S.input.pageUniverse := by
  by_cases hjk : j < S.cacheSize
  · rw [seq_initial S hjk, Instance.pageUniverse, List.mem_toFinset, List.mem_append]
    exact Or.inl (List.getElem_mem _)
  · rw [show j = S.cacheSize + (j - S.cacheSize) by omega]
    exact pageAt_mem_pageUniverse S (by omega)

/-- FIFO's cache lies in the page universe. -/
theorem queue_subset_pageUniverse {i : ℕ} (hi : i ≤ S.count) {x : Page} (hx : x ∈ S.queue i) :
    x ∈ S.input.pageUniverse := by
  obtain ⟨j, _, hj, rfl⟩ := exists_of_mem_queue S hi hx
  exact seq_mem_pageUniverse S (by omega)

/-- The served occurrences of distinct payments are disjoint, identifier-wise. -/
theorem servedIds_nodup :
    ((S.payments.flatMap FIFO.Payment.served).map Occurrence.id).Nodup :=
  FIFO.History.final_servedIds_nodup (δ := S.threshold) S.input

end

end Setup

end PagingWithDelay.RankPotential
