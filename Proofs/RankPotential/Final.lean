import Proofs.RankPotential.Charging
import Proofs.Competitive.AlgorithmCost
import Proofs.Analysis.Amortized
import Algorithm
import Proofs.Basic.Competitive

/-!
# Payment accounting and the competitive guarantees

Summing the per-payment facts of `Charging.lean` over all `M` payments gives
the write-up's "Payment accounting"

  `M + Φ_final - Φ_0 ≤ (k+1)·S + ((k+1)/δ)·D`

(`payment_accounting_missing`, stated additively), where `S` and `D` are the
comparator's fetch count and delay cost and `Φ = ∑_{q ∈ C_ALG \ C_OPT} rank q`
is the write-up's potential, the complement `K - potential` of the one used in
`Charging.lean`.  The three cases enter as three disjoint sets of payments:
`heldSet` (one unit from the online potential change), `droppedSet` (one unit
from an associated offline event, `droppedSet_card_le` and `sum_gain_ge_of`),
and `neverSet` (one unit from the charged delay, `neverSet_delay_le`).

Since `Φ_0 = 0` (`missing_zero`), `paymentCount_le` gives
`M ≤ (k+1)·S + ((k+1)/δ)·D` for every threshold, and at `δ = 1` the main
theorem `competitiveRatio`: `ALG = 2M ≤ (2k+2)·OPT`.
-/

namespace PagingWithDelay.RankPotential

open PagingWithDelay Analysis Finset

variable {Page : Type*} [DecidableEq Page]

noncomputable section

open Classical in
/-- The payments of case 1. -/
def heldSet (S : Setup Page) (comparator : Schedule Page) : Finset ℕ :=
  (Finset.range S.count).filter (Held S comparator)

open Classical in
/-- The payments of case 2. -/
def droppedSet (S : Setup Page) (comparator : Schedule Page) : Finset ℕ :=
  (Finset.range S.count).filter (Dropped S comparator)

open Classical in
/-- The payments of case 3. -/
def neverSet (S : Setup Page) (comparator : Schedule Page) : Finset ℕ :=
  (Finset.range S.count).filter (Never S comparator)

variable {S : Setup Page} {comparator : Schedule Page}

/-- **The cases partition the payments.** -/
theorem card_partition :
    S.count = (heldSet S comparator).card + (droppedSet S comparator).card +
      (neverSet S comparator).card := by
  classical
  have h1 : Disjoint (heldSet S comparator) (droppedSet S comparator) :=
    Finset.disjoint_filter.mpr fun _ _ h h' => h'.1 h
  have h2 : Disjoint (heldSet S comparator ∪ droppedSet S comparator) (neverSet S comparator) := by
    rw [heldSet, droppedSet, ← Finset.filter_or]
    refine Finset.disjoint_filter.mpr fun i hi h h' => ?_
    rcases h with h | ⟨_, n, hlow, hhigh, hmem⟩
    · exact h' _ (windowLow_le (Finset.mem_range.mp hi)) le_rfl h
    · exact h' n hlow hhigh.le hmem
  rw [← Finset.card_union_of_disjoint h1, ← Finset.card_union_of_disjoint h2, heldSet,
    droppedSet, neverSet, ← Finset.filter_or, ← Finset.filter_or, Finset.filter_true_of_mem
      fun i _ => or_assoc.mpr (cases_exhaustive i), Finset.card_range]

/-! ### Telescoping over all payments -/

theorem sum_heldIndicator :
    ∑ i ∈ Finset.range S.count, heldIndicator S comparator i =
      S.cacheSize * (heldSet S comparator).card := by
  classical
  unfold heldIndicator heldSet
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm]

/-- The per-payment identity: potential after, plus the shared count and `k`
per offline event of the interval, equals the potential before plus the
offline gains and `k` if the page was held. -/
theorem step_identity {i : ℕ} (hi : i < S.count) :
    potential S comparator (i + 1) + shared S comparator i +
        S.cacheSize * (eventIndex S comparator (i + 1) - eventIndex S comparator i) =
      potential S comparator i +
        (∑ n ∈ Finset.Ico (eventIndex S comparator i) (eventIndex S comparator (i + 1)),
          gainAt S comparator i n) +
        heldIndicator S comparator i := by
  have := potential_interval (comparator := comparator) hi.le
  have := potential_step_online (comparator := comparator) hi
  omega

/-- The total offline gain, over all events of all intervals. -/
def totalGain (S : Setup Page) (comparator : Schedule Page) : ℕ :=
  ∑ i ∈ Finset.range S.count,
    ∑ n ∈ Finset.Ico (eventIndex S comparator i) (eventIndex S comparator (i + 1)),
      gainAt S comparator i n

/-- **Summed identity.**  `Φ_final + ∑ m_i + k·S' = Φ_0 + (offline gains) + k·|held|`,
with `S'` the number of offline events before the last payment. -/
theorem sum_identity :
    potential S comparator S.count + (∑ i ∈ Finset.range S.count, shared S comparator i) +
        S.cacheSize * eventIndex S comparator S.count =
      potential S comparator 0 + totalGain S comparator +
        S.cacheSize * (heldSet S comparator).card := by
  have hsum := Finset.sum_congr rfl fun i (hi : i ∈ Finset.range S.count) =>
    step_identity (comparator := comparator) (Finset.mem_range.mp hi)
  simp only [Finset.sum_add_distrib] at hsum
  have htel : (∑ i ∈ Finset.range S.count, potential S comparator (i + 1)) +
      potential S comparator 0 =
      potential S comparator S.count + ∑ i ∈ Finset.range S.count, potential S comparator i := by
    rw [← Finset.sum_range_succ', Finset.sum_range_succ_comm]
  have hevents : (∑ i ∈ Finset.range S.count,
      S.cacheSize * (eventIndex S comparator (i + 1) - eventIndex S comparator i)) =
      S.cacheSize * eventIndex S comparator S.count := by
    rw [← Finset.mul_sum, Finset.range_eq_Ico,
      Analysis.sum_Ico_increment_nat eventIndex_monotone (Nat.zero_le _)]
    rfl
  have hheld := sum_heldIndicator (S := S) (comparator := comparator)
  unfold totalGain
  omega

/-! ### The three charges -/

/-- Shared pages: at most `k`, and at most `k - 1` when the page is held. -/
theorem sum_shared_le (feasible : comparator.Feasible S.input) :
    (∑ i ∈ Finset.range S.count, shared S comparator i) + (heldSet S comparator).card ≤
      S.cacheSize * S.count := by
  classical
  have : ∀ i ∈ Finset.range S.count,
      shared S comparator i + (if Held S comparator i then 1 else 0) ≤ S.cacheSize := by
    intro i hi
    have hi := Finset.mem_range.mp hi
    split_ifs with h
    · exact shared_lt_of_held feasible hi h
    · simpa using shared_le i hi.le
  have hsum := Finset.sum_le_sum this
  rwa [Finset.sum_add_distrib, ← Finset.card_filter, Finset.sum_const, smul_eq_mul,
    Finset.card_range, mul_comm] at hsum

/-- The offline event associated with a dropped payment, with the interval it
lies in. -/
theorem dropped_assoc {i : ℕ} (hi : i < S.count) (h : Dropped S comparator i) :
    ∃ x : ℕ × ℕ, x.1 < S.count ∧ eventIndex S comparator x.1 ≤ x.2 ∧
      x.2 < eventIndex S comparator (x.1 + 1) ∧
      windowLow S comparator i ≤ x.2 ∧ x.2 < eventIndex S comparator (i + 1) ∧
      S.pageAt i ∈ lazy S comparator x.2 ∧ S.pageAt i ∉ lazy S comparator (x.2 + 1) := by
  obtain ⟨n, hlow, hhigh, hmem, hnot⟩ := dropped_event h
  obtain ⟨j, hj, hjlow, hjhigh⟩ :=
    exists_interval (hhigh.trans_le (eventIndex_monotone (Nat.succ_le_of_lt hi)))
  exact ⟨(j, n), hj, hjlow, hjhigh, hlow, hhigh, hmem, hnot⟩

open Classical in
/-- The association of case 2: a dropped payment to the last eviction of its
page in its window. -/
def assoc (S : Setup Page) (comparator : Schedule Page) (i : ℕ) : ℕ × ℕ :=
  if h : i < S.count ∧ Dropped S comparator i then (dropped_assoc h.1 h.2).choose else (0, 0)

theorem assoc_spec {i : ℕ} (hi : i < S.count) (h : Dropped S comparator i) :
    (assoc S comparator i).1 < S.count ∧
      eventIndex S comparator (assoc S comparator i).1 ≤ (assoc S comparator i).2 ∧
      (assoc S comparator i).2 < eventIndex S comparator ((assoc S comparator i).1 + 1) ∧
      windowLow S comparator i ≤ (assoc S comparator i).2 ∧
      (assoc S comparator i).2 < eventIndex S comparator (i + 1) ∧
      S.pageAt i ∈ lazy S comparator (assoc S comparator i).2 ∧
      S.pageAt i ∉ lazy S comparator ((assoc S comparator i).2 + 1) := by
  classical
  unfold assoc
  rw [dif_pos ⟨hi, h⟩]
  exact (dropped_assoc hi h).choose_spec

theorem mem_droppedSet {i : ℕ} :
    i ∈ droppedSet S comparator ↔ i < S.count ∧ Dropped S comparator i := by
  classical
  simp [droppedSet]

/-- **No offline event is associated with two payments.** -/
theorem assoc_snd_injOn :
    Set.InjOn (fun i => (assoc S comparator i).2) (droppedSet S comparator) := by
  intro i hi i' hi' heq
  rw [Finset.mem_coe, mem_droppedSet] at hi hi'
  obtain ⟨_, _, _, hlow, hhigh, hmem, hnot⟩ := assoc_spec hi.1 hi.2
  obtain ⟨_, _, _, hlow', hhigh', hmem', hnot'⟩ := assoc_spec hi'.1 hi'.2
  dsimp only at heq
  rw [heq] at hlow hhigh hmem hnot
  exact dropped_event_injective hi.1 hi'.1 hlow hhigh hmem hnot hlow' hhigh' hmem' hnot'

/-- **Case 2 charges an offline event of gain at least `k`.** -/
theorem gain_assoc_ge {i : ℕ} (hi : i < S.count) (h : Dropped S comparator i) :
    S.cacheSize ≤ gainAt S comparator (assoc S comparator i).1 (assoc S comparator i).2 := by
  obtain ⟨hj, hjlow, hjhigh, hlow, hhigh, hmem, hnot⟩ := assoc_spec hi h
  have := pageAt_not_mem_queue_of_mem_window hi hlow hhigh hjlow hjhigh
  exact gainAt_ge_of_evicted_outside hj.le hmem hnot this.2

/-- The events of all intervals, as pairs `(interval, event)`. -/
def intervalEvents (S : Setup Page) (comparator : Schedule Page) : Finset (ℕ × ℕ) :=
  (Finset.range S.count).sigma (fun i =>
    Finset.Ico (eventIndex S comparator i) (eventIndex S comparator (i + 1))) |>.map
      (Equiv.sigmaEquivProd ℕ ℕ).toEmbedding

/-- **The offline gains pay for the dropped payments**, `g` units each when
every associated event has gain at least `g`. -/
theorem sum_gain_ge_of {g : ℕ} (hg : ∀ i, i < S.count → Dropped S comparator i →
      g ≤ gainAt S comparator (assoc S comparator i).1 (assoc S comparator i).2) :
    g * (droppedSet S comparator).card ≤ totalGain S comparator := by
  have htotal : totalGain S comparator =
      ∑ x ∈ intervalEvents S comparator, gainAt S comparator x.1 x.2 := by
    rw [intervalEvents, Finset.sum_map, Finset.sum_sigma]
    rfl
  have hinj : Set.InjOn (assoc S comparator) (droppedSet S comparator) :=
    fun i hi i' hi' h => assoc_snd_injOn hi hi' (congrArg Prod.snd h)
  calc g * (droppedSet S comparator).card
      = ∑ i ∈ droppedSet S comparator, g := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ droppedSet S comparator,
          gainAt S comparator (assoc S comparator i).1 (assoc S comparator i).2 :=
        Finset.sum_le_sum fun i hi => hg i (mem_droppedSet.mp hi).1 (mem_droppedSet.mp hi).2
    _ = ∑ x ∈ (droppedSet S comparator).image (assoc S comparator),
          gainAt S comparator x.1 x.2 := by rw [Finset.sum_image hinj]
    _ ≤ totalGain S comparator := by
        rw [htotal]
        refine Finset.sum_le_sum_of_subset (Finset.image_subset_iff.mpr fun i hi => ?_)
        obtain ⟨hj, hjlow, hjhigh, _⟩ := assoc_spec (mem_droppedSet.mp hi).1 (mem_droppedSet.mp hi).2
        simpa [intervalEvents] using ⟨hj, hjlow, hjhigh⟩

/-- **Each dropped payment uses a distinct offline event before the last
payment.** -/
theorem droppedSet_card_le :
    (droppedSet S comparator).card ≤ eventIndex S comparator S.count := by
  rw [← Finset.card_range (eventIndex S comparator S.count)]
  refine Finset.card_le_card_of_injOn (fun i => (assoc S comparator i).2) (fun i hi => ?_)
    assoc_snd_injOn
  rw [Finset.mem_coe, mem_droppedSet] at hi
  obtain ⟨_, _, _, _, hhigh, _⟩ := assoc_spec hi.1 hi.2
  exact Finset.mem_range.mpr (hhigh.trans_le (eventIndex_monotone (Nat.succ_le_of_lt hi.1)))

/-- The identifiers of the requests served by payment `i`. -/
def servedIds (S : Setup Page) (i : ℕ) : Finset ℕ :=
  ((S.payments[i]?.map FIFO.Payment.served).getD []).map Occurrence.id |>.toFinset

theorem servedIds_eq {i : ℕ} (hi : i < S.count) :
    servedIds S i = ((S.payments[i]).served.map Occurrence.id).toFinset := by
  simp [servedIds, List.getElem?_eq_getElem (show i < S.payments.length from hi)]

/-- The identifiers served by each payment are distinct, and disjoint between payments. -/
theorem servedIds_nodup_flatMap :
    (S.payments.flatMap fun payment => payment.served.map Occurrence.id).Nodup := by
  simpa [List.map_flatMap] using S.servedIds_nodup

theorem servedIds_disjoint {i j : ℕ} (hi : i < S.count) (hj : j < S.count) (hij : i ≠ j) :
    Disjoint (servedIds S i) (servedIds S j) := by
  rw [servedIds_eq hi, servedIds_eq hj, List.disjoint_toFinset_iff_disjoint]
  have hp := (List.nodup_flatMap.mp (servedIds_nodup_flatMap (S := S))).2
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact List.pairwise_iff_getElem.mp hp i j hi hj hlt
  · exact (List.pairwise_iff_getElem.mp hp j i hj hi hlt).symm

theorem mem_neverSet {i : ℕ} :
    i ∈ neverSet S comparator ↔ i < S.count ∧ Never S comparator i := by
  classical
  simp [neverSet]

/-- **Case 3 charges disjoint delay.**  The never-held payments charge `δ`
each to disjoint sets of requests, so `|never|·δ ≤ D`. -/
theorem neverSet_delay_le (feasible : comparator.Feasible S.input) :
    ((neverSet S comparator).card : Cost) * S.threshold ≤ comparator.totalDelay S.input := by
  set w := Competitive.Schedule.requestIdWeight comparator S.input
  have hbatch : ∀ i ∈ neverSet S comparator, S.threshold ≤ ∑ id ∈ servedIds S i, w id := by
    intro i hi
    obtain ⟨hi, hnever⟩ := mem_neverSet.mp hi
    have hnodup := (List.nodup_flatMap.mp (servedIds_nodup_flatMap (S := S))).1 _ (List.getElem_mem hi)
    rw [servedIds_eq hi, List.sum_toFinset w hnodup, List.map_map]
    refine (threshold_le_delay_of_never feasible hi hnever).trans_eq (congrArg List.sum ?_)
    exact List.map_congr_left fun occurrence ho =>
      (Competitive.Schedule.requestIdWeight_eq_requestCost_of_mem_enumerate comparator
        S.input (S.served_authentic hi ho)).symm
  have hsub : ∀ i ∈ neverSet S comparator, servedIds S i ⊆ Finset.range S.input.requests.length := by
    intro i hi id hid
    have hi := (mem_neverSet.mp hi).1
    rw [servedIds_eq hi, List.mem_toFinset, List.mem_map] at hid
    obtain ⟨occurrence, ho, rfl⟩ := hid
    exact Finset.mem_range.mpr
      (Competitive.Schedule.id_lt_of_mem_enumerate (S.served_authentic hi ho))
  calc ((neverSet S comparator).card : Cost) * S.threshold
      = ∑ i ∈ neverSet S comparator, S.threshold := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ neverSet S comparator, ∑ id ∈ servedIds S i, w id := Finset.sum_le_sum hbatch
    _ = ∑ id ∈ (neverSet S comparator).biUnion (servedIds S), w id :=
        (Finset.sum_biUnion fun i hi j hj hij =>
          servedIds_disjoint (mem_neverSet.mp hi).1 (mem_neverSet.mp hj).1 hij).symm
    _ ≤ ∑ id ∈ Finset.range S.input.requests.length, w id :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.biUnion_subset.mpr hsub)
          fun _ _ _ => zero_le _
    _ = comparator.totalDelay S.input := Competitive.Schedule.sum_requestIdWeight_range _ _

/-! ### The write-up's potential

The write-up states the accounting for `Φ = ∑_{q ∈ C_ALG \ C_OPT} rank q`, the
complement `K - potential` of the potential used above
(`Analysis.missingPotential_add_rankPotential`).  With it `Φ_0 = 0`
(`missing_zero`). -/

/-- The write-up's potential `Φ = ∑_{q ∈ C_ALG \ C_OPT} rank q` at the boundary
before interval `i`. -/
def missing (S : Setup Page) (comparator : Schedule Page) (i : ℕ) : ℕ :=
  missingPotential (S.queue i) (lazy S comparator (eventIndex S comparator i))

/-- The two potentials sum to `K` at every boundary. -/
theorem missing_add_potential {i : ℕ} (hi : i ≤ S.count) :
    missing S comparator i + potential S comparator i = triangular S.cacheSize := by
  unfold missing potential
  rw [missingPotential_add_rankPotential (S.queue_nodup hi), S.queue_length hi]

/-- **`Φ_0 = 0`.**  Both caches start as `C₀`. -/
theorem missing_zero (feasible : comparator.Feasible S.input) : missing S comparator 0 = 0 := by
  unfold missing
  rw [S.queue_zero, eventIndex, lazy, Analysis.lazyCache_zero, feasible.initialCache,
    missingPotential_toFinset]

/-! ### Payment accounting -/

/-- **Payment accounting, combinatorial form, with a general fetch charge.**
If every associated offline event has gain at least `g`, then with `c + g = 2k+1`
— `c` is the charge per offline fetch, `k+1` in general and `k` on `k+1`
pages — and `E` the number of offline events before the last payment and `C`
the never-held payments, `M + Φ_final ≤ c·E + (k+1)·|C| + Φ_0`. -/
theorem payment_accounting_nat_of_gain (feasible : comparator.Feasible S.input)
    {c g : ℕ} (hcg : c + g = 2 * S.cacheSize + 1) (hgk : g ≤ S.cacheSize + 1)
    (hg : ∀ i, i < S.count → Dropped S comparator i →
      g ≤ gainAt S comparator (assoc S comparator i).1 (assoc S comparator i).2) :
    S.count + missing S comparator S.count ≤
      c * eventIndex S comparator S.count +
        (S.cacheSize + 1) * (neverSet S comparator).card + missing S comparator 0 := by
  have h0 := missing_add_potential (S := S) (comparator := comparator) (Nat.zero_le _)
  have h1 := missing_add_potential (S := S) (comparator := comparator) le_rfl
  have h2 := sum_identity (S := S) (comparator := comparator)
  have h3 := sum_shared_le feasible
  have h4 := sum_gain_ge_of hg
  have h5 := card_partition (S := S) (comparator := comparator)
  have h6 : S.cacheSize * S.count = S.cacheSize * (heldSet S comparator).card +
      S.cacheSize * (droppedSet S comparator).card +
      S.cacheSize * (neverSet S comparator).card := by
    rw [h5]; ring
  -- `c = k + (k+1-g)`: the extra `k+1-g` per offline event pays for the dropped payments
  have h7 : c * eventIndex S comparator S.count =
      S.cacheSize * eventIndex S comparator S.count +
        (S.cacheSize + 1 - g) * eventIndex S comparator S.count := by
    rw [← Nat.add_mul]; congr 1; omega
  have h8 : g * (droppedSet S comparator).card + (S.cacheSize + 1 - g) *
      (droppedSet S comparator).card = (S.cacheSize + 1) * (droppedSet S comparator).card := by
    rw [← Nat.add_mul]; congr 1; omega
  have h9 : (S.cacheSize + 1 - g) * (droppedSet S comparator).card ≤
      (S.cacheSize + 1 - g) * eventIndex S comparator S.count :=
    Nat.mul_le_mul_left _ droppedSet_card_le
  nlinarith

/-- **Payment accounting with a general fetch charge**, in the write-up's
potential: `M + Φ_final ≤ c·S + ((k+1)/δ)·D + Φ_0` whenever every associated
offline event has gain at least `g = 2k+1-c`. -/
theorem payment_accounting_missing_of_gain (hδ : 0 < S.threshold) (feasible : comparator.Feasible S.input)
    {c g : ℕ} (hcg : c + g = 2 * S.cacheSize + 1) (hgk : g ≤ S.cacheSize + 1)
    (hg : ∀ i, i < S.count → Dropped S comparator i →
      g ≤ gainAt S comparator (assoc S comparator i).1 (assoc S comparator i).2) :
    (S.count : Cost) + missing S comparator S.count ≤
      (c : ℕ) * comparator.fetchCount +
        ((S.cacheSize + 1 : ℕ) / S.threshold) * comparator.totalDelay S.input +
        missing S comparator 0 := by
  have hE : (eventIndex S comparator S.count : Cost) ≤ comparator.fetchCount := by
    exact_mod_cast eventIndex_le_length S.count
  have hC : ((neverSet S comparator).card : Cost) ≤
      comparator.totalDelay S.input / S.threshold :=
    (le_div_iff₀ hδ).mpr (neverSet_delay_le feasible)
  calc (S.count : Cost) + missing S comparator S.count
      ≤ (c : ℕ) * (eventIndex S comparator S.count : Cost) +
          (S.cacheSize + 1 : ℕ) * ((neverSet S comparator).card : Cost) +
          missing S comparator 0 := by
        exact_mod_cast payment_accounting_nat_of_gain feasible hcg hgk hg
    _ ≤ (c : ℕ) * comparator.fetchCount +
          (S.cacheSize + 1 : ℕ) * (comparator.totalDelay S.input / S.threshold) +
          missing S comparator 0 := by gcongr
    _ = _ := by rw [mul_div_assoc']; ring

/-- **Payment accounting** in the write-up's form (general threshold):
`M + Φ_final - Φ_0 ≤ (k+1)·S + ((k+1)/δ)·D`, stated additively, with
`Φ = ∑_{q ∈ C_ALG \ C_OPT} rank q`.  Here `C_OPT` is the comparator's lazy
cache, and `Φ_final` is taken just after the last FIFO payment, counting the
comparator events stamped no later than it. -/
theorem payment_accounting_missing (hδ : 0 < S.threshold) (feasible : comparator.Feasible S.input) :
    (S.count : Cost) + missing S comparator S.count ≤
      (S.cacheSize + 1 : ℕ) * comparator.fetchCount +
        ((S.cacheSize + 1 : ℕ) / S.threshold) * comparator.totalDelay S.input +
        missing S comparator 0 :=
  payment_accounting_missing_of_gain hδ feasible (c := S.cacheSize + 1) (g := S.cacheSize)
    (by ring) (Nat.le_succ _) (fun _ hi h => gain_assoc_ge hi h)

/-- **`M ≤ c·S + ((k+1)/δ)·D`** whenever every associated offline event has
gain at least `2k+1-c`, from `Φ_0 = 0 ≤ Φ_final`. -/
theorem paymentCount_le_of_gain (hδ : 0 < S.threshold) (feasible : comparator.Feasible S.input)
    {c g : ℕ} (hcg : c + g = 2 * S.cacheSize + 1) (hgk : g ≤ S.cacheSize + 1)
    (hg : ∀ i, i < S.count → Dropped S comparator i →
      g ≤ gainAt S comparator (assoc S comparator i).1 (assoc S comparator i).2) :
    (S.count : Cost) ≤
      (c : ℕ) * comparator.fetchCount +
        ((S.cacheSize + 1 : ℕ) / S.threshold) * comparator.totalDelay S.input := by
  have h := payment_accounting_missing_of_gain hδ feasible hcg hgk hg
  rw [missing_zero feasible, Nat.cast_zero, add_zero] at h
  exact le_self_add.trans h

/-- **`M ≤ (k+1)·S + ((k+1)/δ)·D`** for every positive threshold. -/
theorem paymentCount_le (hδ : 0 < S.threshold) (feasible : comparator.Feasible S.input) :
    (S.count : Cost) ≤
      (S.cacheSize + 1 : ℕ) * comparator.fetchCount +
        ((S.cacheSize + 1 : ℕ) / S.threshold) * comparator.totalDelay S.input :=
  paymentCount_le_of_gain hδ feasible (c := S.cacheSize + 1) (g := S.cacheSize) (by ring)
    (Nat.le_succ _) (fun _ hi h => gain_assoc_ge hi h)

/-- `ALG = (1+δ)·M`, so `M ≤ a·S + a·D = a·OPT` gives `ALG ≤ (1+δ)·a·OPT`. -/
theorem totalCost_le_of_paymentCount_le {a : Cost}
    (h : (S.count : Cost) ≤ a * comparator.fetchCount + a * comparator.totalDelay S.input) :
    (FIFO.schedule S.trigger S.input).totalCost S.input ≤
      (1 + S.threshold) * a * comparator.totalCost S.input := by
  have hcost := FIFO.algorithmCostClaim S.trigger S.input
  unfold FIFO.AlgorithmCostClaim FIFO.algorithmCost at hcost
  rw [hcost, mul_assoc, Schedule.totalCost, mul_add]
  exact mul_le_mul_right h _

end

/-! ### The main theorem -/

/-- **The main theorem.**  Threshold-one FIFO is `(2k+2)`-competitive with no
additive constant: `ALG = 2M` and `M ≤ (k+1)·(S + D) = (k+1)·OPT`. -/
theorem competitiveRatio (input : Instance Page) (comparator : Schedule Page)
    (feasible : comparator.Feasible input) :
    (FIFO.schedule (.threshold 1) input).totalCost input ≤
      (2 * input.cacheSize + 2 : ℕ) * comparator.totalCost input := by
  have hM := paymentCount_le (S := ⟨.threshold 1, input⟩) zero_lt_one feasible
  simp only [Setup.threshold, FIFO.Trigger.level_threshold, div_one] at hM
  refine (totalCost_le_of_paymentCount_le hM).trans_eq ?_
  simp only [Setup.threshold, FIFO.Trigger.level_threshold]
  push_cast
  ring

/-- **The main theorem** in the form `PagingWithDelay.lean` states it:
threshold-one FIFO is strictly `(2k+2)`-competitive. -/
theorem strictlyCompetitive :
    (FIFO.algorithm (Page := Page) fun _ => 1).StrictlyCompetitive fun k => 2 * k + 2 :=
  Algorithm.strictlyCompetitive_of_schedules fun input _ comparator feasible => by
    simpa using competitiveRatio input comparator feasible

end PagingWithDelay.RankPotential
