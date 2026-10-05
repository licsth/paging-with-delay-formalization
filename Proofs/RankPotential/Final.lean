import Proofs.RankPotential.Charging
import Proofs.Competitive.AlgorithmCost
import Proofs.Analysis.Amortized

/-!
# Payment accounting and the competitive guarantees

Summing the per-payment facts of `Charging.lean` over all `M` payments gives
the write-up's "Payment accounting", in complement form:

  `M ≤ (k+1)·S + ((k+1)/δ)·D + Φ_final - Φ_0`

(`payment_accounting`, stated additively as `M + Φ_0 ≤ … + Φ_final`), where
`S` and `D` are the comparator's fetch count and delay cost.  The three cases
enter as three disjoint sets of payments: `heldSet` (one unit from the online
potential change), `droppedSet` (one unit from an associated offline event,
`droppedSet_card_le` and `sum_gain_ge_of`), and `neverSet` (one unit from the
charged delay, `neverSet_delay_le`).

The write-up's potential is the complement `Φ = ∑_{q ∈ C_ALG \ C_OPT} rank q`
of the one used here; `payment_accounting_missing` restates the accounting for
it, as `M + Φ_final - Φ_0 ≤ (k+1)·S + ((k+1)/δ)·D` with `Φ_0 = 0`
(`missing_zero`).

Since `Φ_final ≤ Φ_0` (`potential_zero_eq_triangular`, `potential_le_triangular`),
`paymentCount_le` gives `M ≤ (k+1)·S + ((k+1)/δ)·D` for every threshold, and
at `δ = 1` the main theorem `competitiveRatio`: `ALG = 2M ≤ (2k+2)·OPT`.
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
  have h1 : Disjoint (heldSet S comparator) (droppedSet S comparator) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [heldSet, droppedSet, Finset.mem_filter] at hi hi'
    exact hi'.2.1 hi.2
  have h2 : Disjoint (heldSet S comparator ∪ droppedSet S comparator) (neverSet S comparator) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [heldSet, droppedSet, neverSet, Finset.mem_union, Finset.mem_filter] at hi hi'
    rcases hi with hi | hi
    · exact hi'.2 _ (windowLow_le (Finset.mem_range.mp hi.1)) le_rfl hi.2
    · obtain ⟨n, hlow, hhigh, hmem⟩ := hi.2.2
      exact hi'.2 n hlow hhigh.le hmem
  have hcover : heldSet S comparator ∪ droppedSet S comparator ∪ neverSet S comparator =
      Finset.range S.count := by
    ext i
    simp only [heldSet, droppedSet, neverSet, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hi
      rcases cases_exhaustive (S := S) (comparator := comparator) i with h | h | h
      · exact Or.inl (Or.inl ⟨hi, h⟩)
      · exact Or.inl (Or.inr ⟨hi, h⟩)
      · exact Or.inr ⟨hi, h⟩
  rw [← Finset.card_range S.count, ← hcover, Finset.card_union_of_disjoint h2,
    Finset.card_union_of_disjoint h1]

/-! ### Telescoping over all payments -/

open Classical in
/-- `k·[pageAt i ∈ C_OPT]`. -/
def heldIndicator (S : Setup Page) (comparator : Schedule Page) (i : ℕ) : ℕ :=
  if Held S comparator i then S.cacheSize else 0

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
  classical
  have hint := potential_interval (comparator := comparator) hi.le
  unfold heldIndicator
  by_cases h : Held S comparator i
  · have := potential_step_online_of_held hi h
    rw [if_pos h]
    omega
  · have := potential_step_online_of_not_held hi h
    rw [if_neg h]
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
  classical
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
  rw [Finset.sum_add_distrib, ← Finset.card_filter, Finset.sum_const, smul_eq_mul,
    Finset.card_range, mul_comm] at hsum
  exact hsum

/-- The offline event associated with a dropped payment, with the interval it
lies in. -/
theorem dropped_assoc {i : ℕ} (hi : i < S.count) (h : Dropped S comparator i) :
    ∃ x : ℕ × ℕ, x.1 < S.count ∧ eventIndex S comparator x.1 ≤ x.2 ∧
      x.2 < eventIndex S comparator (x.1 + 1) ∧
      windowLow S comparator i ≤ x.2 ∧ x.2 < eventIndex S comparator (i + 1) ∧
      S.pageAt i ∈ Analysis.lazyCache S.cacheSize S.input.pageUniverse comparator x.2 ∧
      S.pageAt i ∉ Analysis.lazyCache S.cacheSize S.input.pageUniverse comparator (x.2 + 1) := by
  obtain ⟨n, hlow, hhigh, hmem, hnot⟩ := dropped_event h
  have hn : n < eventIndex S comparator S.count :=
    hhigh.trans_le (eventIndex_monotone (Nat.succ_le_of_lt hi))
  obtain ⟨j, hj, hjlow, hjhigh⟩ := exists_interval hn
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
      S.pageAt i ∈ Analysis.lazyCache S.cacheSize S.input.pageUniverse comparator (assoc S comparator i).2 ∧
      S.pageAt i ∉ Analysis.lazyCache S.cacheSize S.input.pageUniverse comparator ((assoc S comparator i).2 + 1) := by
  classical
  unfold assoc
  rw [dif_pos ⟨hi, h⟩]
  exact (dropped_assoc hi h).choose_spec

/-- **No offline event is associated with two payments.** -/
theorem assoc_injOn : Set.InjOn (assoc S comparator) (droppedSet S comparator) := by
  classical
  intro i hi i' hi' heq
  simp only [droppedSet, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hi hi'
  obtain ⟨_, _, _, hlow, hhigh, hmem, hnot⟩ := assoc_spec hi.1 hi.2
  obtain ⟨_, _, _, hlow', hhigh', hmem', hnot'⟩ := assoc_spec hi'.1 hi'.2
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

theorem totalGain_eq :
    totalGain S comparator = ∑ x ∈ intervalEvents S comparator, gainAt S comparator x.1 x.2 := by
  unfold totalGain intervalEvents
  rw [Finset.sum_map, Finset.sum_sigma]
  rfl

theorem assoc_mem_intervalEvents {i : ℕ} (hi : i < S.count) (h : Dropped S comparator i) :
    assoc S comparator i ∈ intervalEvents S comparator := by
  obtain ⟨hj, hjlow, hjhigh, _⟩ := assoc_spec hi h
  unfold intervalEvents
  rw [Finset.mem_map]
  refine ⟨⟨(assoc S comparator i).1, (assoc S comparator i).2⟩, ?_, rfl⟩
  rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico]
  exact ⟨hj, hjlow, hjhigh⟩

/-- **The offline gains pay for the dropped payments**, `g` units each when
every associated event has gain at least `g`. -/
theorem sum_gain_ge_of {g : ℕ} (hg : ∀ i, i < S.count → Dropped S comparator i →
      g ≤ gainAt S comparator (assoc S comparator i).1 (assoc S comparator i).2) :
    g * (droppedSet S comparator).card ≤ totalGain S comparator := by
  classical
  rw [totalGain_eq]
  calc g * (droppedSet S comparator).card
      = ∑ i ∈ droppedSet S comparator, g := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ droppedSet S comparator,
          gainAt S comparator (assoc S comparator i).1 (assoc S comparator i).2 := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [droppedSet, Finset.mem_filter, Finset.mem_range] at hi
        exact hg i hi.1 hi.2
    _ = ∑ x ∈ (droppedSet S comparator).image (assoc S comparator),
          gainAt S comparator x.1 x.2 := by
        rw [Finset.sum_image assoc_injOn]
    _ ≤ ∑ x ∈ intervalEvents S comparator, gainAt S comparator x.1 x.2 := by
        apply Finset.sum_le_sum_of_subset
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        simp only [droppedSet, Finset.mem_filter, Finset.mem_range] at hi
        exact assoc_mem_intervalEvents hi.1 hi.2

/-- **Each dropped payment uses a distinct offline event before the last
payment.** -/
theorem droppedSet_card_le :
    (droppedSet S comparator).card ≤ eventIndex S comparator S.count := by
  classical
  rw [← Finset.card_range (eventIndex S comparator S.count)]
  apply Finset.card_le_card_of_injOn (fun i => (assoc S comparator i).2)
  · intro i hi
    simp only [droppedSet, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hi
    obtain ⟨_, _, _, _, hhigh, _⟩ := assoc_spec hi.1 hi.2
    simp only [Finset.coe_range, Set.mem_Iio]
    exact hhigh.trans_le (eventIndex_monotone (Nat.succ_le_of_lt hi.1))
  · intro i hi i' hi' heq
    apply assoc_injOn hi hi'
    simp only at heq
    simp only [droppedSet, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hi hi'
    obtain ⟨_, hlow, hhigh, _⟩ := assoc_spec hi.1 hi.2
    obtain ⟨_, hlow', hhigh', _⟩ := assoc_spec hi'.1 hi'.2
    -- the event determines the interval
    have h1 : (assoc S comparator i).1 = (assoc S comparator i').1 := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have := eventIndex_monotone (S := S) (comparator := comparator)
          (Nat.succ_le_of_lt hlt)
        exact absurd (hhigh.trans_le (this.trans (hlow'.trans heq.symm.le))) (lt_irrefl _)
      · have := eventIndex_monotone (S := S) (comparator := comparator)
          (Nat.succ_le_of_lt hlt)
        exact absurd (hhigh'.trans_le (this.trans (hlow.trans heq.le))) (lt_irrefl _)
    exact Prod.ext h1 heq

/-- The identifiers of the requests served by payment `i`. -/
def servedIds (S : Setup Page) (i : ℕ) : Finset ℕ :=
  ((S.payments[i]?.map FIFO.Payment.served).getD []).map Occurrence.id |>.toFinset

theorem servedIds_eq {i : ℕ} (hi : i < S.count) :
    servedIds S i = ((S.payments[i]).served.map Occurrence.id).toFinset := by
  simp [servedIds, List.getElem?_eq_getElem (show i < S.payments.length from hi)]

theorem servedIds_disjoint {i j : ℕ} (hi : i < S.count) (hj : j < S.count) (hij : i ≠ j) :
    Disjoint (servedIds S i) (servedIds S j) := by
  rw [servedIds_eq hi, servedIds_eq hj, List.disjoint_toFinset_iff_disjoint]
  have hn : (S.payments.flatMap fun payment => payment.served.map Occurrence.id).Nodup := by
    have heq : ∀ ps : List (FIFO.Payment Page),
        (ps.flatMap FIFO.Payment.served).map Occurrence.id =
          ps.flatMap (fun payment => payment.served.map Occurrence.id) := by
      intro ps
      induction ps with
      | nil => rfl
      | cons p ps ih => simp [ih]
    rw [← heq]
    exact S.servedIds_nodup
  have hp := (List.nodup_flatMap.mp hn).2
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact List.pairwise_iff_getElem.mp hp i j hi hj hlt
  · exact (List.pairwise_iff_getElem.mp hp j i hj hi hlt).symm

/-- **Case 3 charges disjoint delay.**  The never-held payments charge `δ`
each to disjoint sets of requests, so `|never|·δ ≤ D`. -/
theorem neverSet_delay_le (feasible : comparator.Feasible S.input) :
    ((neverSet S comparator).card : Cost) * S.threshold ≤ comparator.totalDelay S.input := by
  classical
  set w := Competitive.Schedule.requestIdWeight comparator S.input with hw
  have hbatch : ∀ i ∈ neverSet S comparator, S.threshold ≤ ∑ id ∈ servedIds S i, w id := by
    intro i hi
    simp only [neverSet, Finset.mem_filter, Finset.mem_range] at hi
    have hi1 : i < S.count := hi.1
    have hnodup : ((S.payments[i]).served.map Occurrence.id).Nodup := by
      have hall := S.servedIds_nodup
      have hsub : List.Sublist (S.payments[i]).served
          (S.payments.flatMap FIFO.Payment.served) := by
        rw [List.flatMap_def]
        exact List.sublist_flatten_of_mem (List.mem_map_of_mem (List.getElem_mem hi1))
      exact hall.sublist (hsub.map Occurrence.id)
    rw [servedIds_eq hi1, List.sum_toFinset w hnodup, List.map_map]
    refine (threshold_le_delay_of_never feasible hi1 hi.2).trans (le_of_eq ?_)
    apply congrArg List.sum
    apply List.map_congr_left
    intro occurrence ho
    exact (Competitive.Schedule.requestIdWeight_eq_requestCost_of_mem_enumerate comparator
      S.input (S.served_authentic hi1 ho)).symm
  have hsub : ∀ i ∈ neverSet S comparator, servedIds S i ⊆ Finset.range S.input.requests.length := by
    intro i hi id hid
    simp only [neverSet, Finset.mem_filter, Finset.mem_range] at hi
    rw [servedIds_eq hi.1, List.mem_toFinset, List.mem_map] at hid
    obtain ⟨occurrence, ho, rfl⟩ := hid
    exact Finset.mem_range.mpr
      (Competitive.Schedule.id_lt_of_mem_enumerate (S.served_authentic hi.1 ho))
  have hdisj : ∀ i ∈ neverSet S comparator, ∀ j ∈ neverSet S comparator, i ≠ j →
      Disjoint (servedIds S i) (servedIds S j) := by
    intro i hi j hj hij
    simp only [neverSet, Finset.mem_filter, Finset.mem_range] at hi hj
    exact servedIds_disjoint hi.1 hj.1 hij
  calc ((neverSet S comparator).card : Cost) * S.threshold
      = ∑ i ∈ neverSet S comparator, S.threshold := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ neverSet S comparator, ∑ id ∈ servedIds S i, w id := Finset.sum_le_sum hbatch
    _ = ∑ id ∈ (neverSet S comparator).biUnion (servedIds S), w id :=
        (Finset.sum_biUnion (fun i hi j hj hij =>
          hdisj i (Finset.mem_coe.mp hi) j (Finset.mem_coe.mp hj) hij)).symm
    _ ≤ ∑ id ∈ Finset.range S.input.requests.length, w id := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.biUnion_subset.mpr hsub
        · intros; exact zero_le _
    _ = comparator.totalDelay S.input := Competitive.Schedule.sum_requestIdWeight_range _ _

/-! ### Payment accounting -/

/-- **Payment accounting, combinatorial form, with a general fetch charge.**
If every associated offline event has gain at least `g`, then with `c + g = 2k+1`
— `c` is the charge per offline fetch, `k+1` in general and `k` on `k+1`
pages — and `E` the number of offline events before the last payment and `C`
the never-held payments, `M + Φ_0 ≤ c·E + (k+1)·|C| + Φ_final`. -/
theorem payment_accounting_nat_of_gain (feasible : comparator.Feasible S.input)
    {c g : ℕ} (hcg : c + g = 2 * S.cacheSize + 1) (hgk : g ≤ S.cacheSize + 1)
    (hg : ∀ i, i < S.count → Dropped S comparator i →
      g ≤ gainAt S comparator (assoc S comparator i).1 (assoc S comparator i).2) :
    S.count + potential S comparator 0 ≤
      c * eventIndex S comparator S.count +
        (S.cacheSize + 1) * (neverSet S comparator).card + potential S comparator S.count := by
  have h1 := sum_identity (S := S) (comparator := comparator)
  have h2 := sum_shared_le feasible
  have h3 := sum_gain_ge_of hg
  have h4 := droppedSet_card_le (S := S) (comparator := comparator)
  have h5 := card_partition (S := S) (comparator := comparator)
  have h6 : S.cacheSize * S.count = S.cacheSize * (heldSet S comparator).card +
      S.cacheSize * (droppedSet S comparator).card +
      S.cacheSize * (neverSet S comparator).card := by
    rw [h5]; ring
  have h7 : c * eventIndex S comparator S.count =
      S.cacheSize * eventIndex S comparator S.count +
        (S.cacheSize + 1 - g) * eventIndex S comparator S.count := by
    rw [← Nat.add_mul]; congr 1; omega
  have h8 : g * (droppedSet S comparator).card + (S.cacheSize + 1 - g) *
      (droppedSet S comparator).card = (S.cacheSize + 1) * (droppedSet S comparator).card := by
    rw [← Nat.add_mul]; congr 1; omega
  have h9 : (S.cacheSize + 1 - g) * (droppedSet S comparator).card ≤
      (S.cacheSize + 1 - g) * eventIndex S comparator S.count := Nat.mul_le_mul_left _ h4
  nlinarith

/-- **Payment accounting, combinatorial form.**  With `E` the number of offline
events before the last payment and `C` the never-held payments,
`M + Φ_0 ≤ (k+1)·E + (k+1)·|C| + Φ_final`. -/
theorem payment_accounting_nat (feasible : comparator.Feasible S.input) :
    S.count + potential S comparator 0 ≤
      (S.cacheSize + 1) * eventIndex S comparator S.count +
        (S.cacheSize + 1) * (neverSet S comparator).card + potential S comparator S.count :=
  payment_accounting_nat_of_gain feasible (c := S.cacheSize + 1) (g := S.cacheSize) (by ring) (Nat.le_succ _)
    (fun i hi h => gain_assoc_ge hi h)

/-- **Payment accounting with a general fetch charge**:
`M + Φ_0 ≤ c·S + ((k+1)/δ)·D + Φ_final` whenever every associated offline
event has gain at least `g = 2k+1-c`. -/
theorem payment_accounting_of_gain (feasible : comparator.Feasible S.input)
    {c g : ℕ} (hcg : c + g = 2 * S.cacheSize + 1) (hgk : g ≤ S.cacheSize + 1)
    (hg : ∀ i, i < S.count → Dropped S comparator i →
      g ≤ gainAt S comparator (assoc S comparator i).1 (assoc S comparator i).2) :
    (S.count : Cost) + potential S comparator 0 ≤
      (c : ℕ) * comparator.fetchCount +
        ((S.cacheSize + 1 : ℕ) / S.threshold) * comparator.totalDelay S.input +
        potential S comparator S.count := by
  have hnat := payment_accounting_nat_of_gain feasible hcg hgk hg
  have hE : (eventIndex S comparator S.count : Cost) ≤ comparator.fetchCount := by
    exact_mod_cast eventIndex_le_length (S := S) (comparator := comparator) S.count
  have hC : ((neverSet S comparator).card : Cost) ≤
      comparator.totalDelay S.input / S.threshold := by
    rw [le_div_iff₀ S.threshold_pos]
    exact neverSet_delay_le feasible
  have hcast : (S.count : Cost) + potential S comparator 0 ≤
      (c : ℕ) * (eventIndex S comparator S.count : Cost) +
        (S.cacheSize + 1 : ℕ) * ((neverSet S comparator).card : Cost) +
        potential S comparator S.count := by
    exact_mod_cast hnat
  calc (S.count : Cost) + potential S comparator 0
      ≤ (c : ℕ) * (eventIndex S comparator S.count : Cost) +
          (S.cacheSize + 1 : ℕ) * ((neverSet S comparator).card : Cost) +
          potential S comparator S.count := hcast
    _ ≤ (c : ℕ) * comparator.fetchCount +
          (S.cacheSize + 1 : ℕ) * (comparator.totalDelay S.input / S.threshold) +
          potential S comparator S.count := by gcongr
    _ = _ := by rw [mul_div_assoc']; ring

/-- **Payment accounting** (the write-up's lemma, general threshold):
`M + Φ_0 ≤ (k+1)·S + ((k+1)/δ)·D + Φ_final`, with `S` the comparator's fetch
count and `D` its delay cost. -/
theorem payment_accounting (feasible : comparator.Feasible S.input) :
    (S.count : Cost) + potential S comparator 0 ≤
      (S.cacheSize + 1 : ℕ) * comparator.fetchCount +
        ((S.cacheSize + 1 : ℕ) / S.threshold) * comparator.totalDelay S.input +
        potential S comparator S.count :=
  payment_accounting_of_gain feasible (c := S.cacheSize + 1) (g := S.cacheSize) (by ring) (Nat.le_succ _)
    (fun i hi h => gain_assoc_ge hi h)

/-! ### The potentials at both ends -/

/-- **`Φ_0 = K`.**  Both caches start as `C₀`. -/
theorem potential_zero_eq_triangular (feasible : comparator.Feasible S.input) :
    potential S comparator 0 = triangular S.cacheSize := by
  unfold potential
  rw [S.queue_zero, eventIndex, Analysis.lazyCache_zero, feasible.initialCache,
    rankPotential_toFinset S.input.initialCache_nodup, S.initialCache_length]

/-- **`Φ ≤ K`** at every boundary. -/
theorem potential_le_triangular {i : ℕ} (hi : i ≤ S.count) :
    potential S comparator i ≤ triangular S.cacheSize := by
  unfold potential
  have := rankPotential_le_triangular (S.queue_nodup hi)
    (Analysis.lazyCache S.cacheSize S.input.pageUniverse comparator (eventIndex S comparator i))
  rwa [S.queue_length hi] at this

/-- `Φ_final ≤ Φ_0`. -/
theorem potential_final_le_zero (feasible : comparator.Feasible S.input) :
    (potential S comparator S.count : Cost) ≤ potential S comparator 0 := by
  rw [potential_zero_eq_triangular feasible]
  exact_mod_cast potential_le_triangular (comparator := comparator) le_rfl

/-! ### The write-up's potential

The write-up states the accounting for `Φ = ∑_{q ∈ C_ALG \ C_OPT} rank q`, the
complement `K - potential` of the potential used above
(`Analysis.missingPotential_add_rankPotential`).  With it `Φ_0 = 0`
(`missing_zero`) and the accounting reads `M + Φ_final - Φ_0 ≤ …`
(`payment_accounting_missing`). -/

/-- The write-up's potential `Φ = ∑_{q ∈ C_ALG \ C_OPT} rank q` at the boundary
before interval `i`. -/
def missing (S : Setup Page) (comparator : Schedule Page) (i : ℕ) : ℕ :=
  missingPotential (S.queue i)
    (Analysis.lazyCache S.cacheSize S.input.pageUniverse comparator (eventIndex S comparator i))

/-- The two potentials sum to `K` at every boundary. -/
theorem missing_add_potential {i : ℕ} (hi : i ≤ S.count) :
    missing S comparator i + potential S comparator i = triangular S.cacheSize := by
  unfold missing potential
  rw [missingPotential_add_rankPotential (S.queue_nodup hi), S.queue_length hi]

/-- **`Φ_0 = 0`.**  Both caches start as `C₀`. -/
theorem missing_zero (feasible : comparator.Feasible S.input) : missing S comparator 0 = 0 := by
  have h := missing_add_potential (S := S) (comparator := comparator) (Nat.zero_le _)
  rw [potential_zero_eq_triangular feasible] at h
  omega

/-- **Payment accounting with a general fetch charge**, in the write-up's
potential: `M + Φ_final ≤ c·S + ((k+1)/δ)·D + Φ_0`. -/
theorem payment_accounting_missing_of_gain (feasible : comparator.Feasible S.input)
    {c g : ℕ} (hcg : c + g = 2 * S.cacheSize + 1) (hgk : g ≤ S.cacheSize + 1)
    (hg : ∀ i, i < S.count → Dropped S comparator i →
      g ≤ gainAt S comparator (assoc S comparator i).1 (assoc S comparator i).2) :
    (S.count : Cost) + missing S comparator S.count ≤
      (c : ℕ) * comparator.fetchCount +
        ((S.cacheSize + 1 : ℕ) / S.threshold) * comparator.totalDelay S.input +
        missing S comparator 0 := by
  have h := payment_accounting_of_gain feasible hcg hgk hg
  have e1 : (missing S comparator S.count : Cost) + potential S comparator S.count =
      triangular S.cacheSize := by exact_mod_cast missing_add_potential le_rfl
  have e0 : (missing S comparator 0 : Cost) + potential S comparator 0 =
      triangular S.cacheSize := by exact_mod_cast missing_add_potential (Nat.zero_le _)
  refine le_of_add_le_add_right (a := (potential S comparator 0 : Cost)) ?_
  calc (S.count : Cost) + missing S comparator S.count + potential S comparator 0
      = ((S.count : Cost) + potential S comparator 0) + missing S comparator S.count := by ring
    _ ≤ ((c : ℕ) * comparator.fetchCount +
          ((S.cacheSize + 1 : ℕ) / S.threshold) * comparator.totalDelay S.input +
          potential S comparator S.count) + missing S comparator S.count := by gcongr
    _ = (c : ℕ) * comparator.fetchCount +
          ((S.cacheSize + 1 : ℕ) / S.threshold) * comparator.totalDelay S.input +
          ((missing S comparator S.count : Cost) + potential S comparator S.count) := by ring
    _ = (c : ℕ) * comparator.fetchCount +
          ((S.cacheSize + 1 : ℕ) / S.threshold) * comparator.totalDelay S.input +
          ((missing S comparator 0 : Cost) + potential S comparator 0) := by rw [e1, e0]
    _ = _ := by ring

/-- **Payment accounting** in the write-up's form (general threshold):
`M + Φ_final - Φ_0 ≤ (k+1)·S + ((k+1)/δ)·D`, stated additively, with
`Φ = ∑_{q ∈ C_ALG \ C_OPT} rank q`.  Here `C_OPT` is the comparator's lazy
cache, and `Φ_final` is taken just after the last FIFO payment, counting the
comparator events stamped no later than it. -/
theorem payment_accounting_missing (feasible : comparator.Feasible S.input) :
    (S.count : Cost) + missing S comparator S.count ≤
      (S.cacheSize + 1 : ℕ) * comparator.fetchCount +
        ((S.cacheSize + 1 : ℕ) / S.threshold) * comparator.totalDelay S.input +
        missing S comparator 0 :=
  payment_accounting_missing_of_gain feasible (c := S.cacheSize + 1) (g := S.cacheSize)
    (by ring) (Nat.le_succ _) (fun i hi h => gain_assoc_ge hi h)

/-- **`M ≤ c·S + ((k+1)/δ)·D`** whenever every associated offline event has
gain at least `2k+1-c`. -/
theorem paymentCount_le_of_gain (feasible : comparator.Feasible S.input)
    {c g : ℕ} (hcg : c + g = 2 * S.cacheSize + 1) (hgk : g ≤ S.cacheSize + 1)
    (hg : ∀ i, i < S.count → Dropped S comparator i →
      g ≤ gainAt S comparator (assoc S comparator i).1 (assoc S comparator i).2) :
    (S.count : Cost) ≤
      (c : ℕ) * comparator.fetchCount +
        ((S.cacheSize + 1 : ℕ) / S.threshold) * comparator.totalDelay S.input :=
  le_of_add_le_add_right ((payment_accounting_of_gain feasible hcg hgk hg).trans
    (by have := potential_final_le_zero feasible; gcongr))

/-- **`M ≤ (k+1)·S + ((k+1)/δ)·D`** for every positive threshold. -/
theorem paymentCount_le (feasible : comparator.Feasible S.input) :
    (S.count : Cost) ≤
      (S.cacheSize + 1 : ℕ) * comparator.fetchCount +
        ((S.cacheSize + 1 : ℕ) / S.threshold) * comparator.totalDelay S.input :=
  paymentCount_le_of_gain feasible (c := S.cacheSize + 1) (g := S.cacheSize) (by ring) (Nat.le_succ _)
    (fun i hi h => gain_assoc_ge hi h)

end

/-! ### The main theorem -/

/-- The setup of threshold-one FIFO on a instance. -/
noncomputable def setupOne (input : Instance Page) : Setup Page where
  cacheSize := input.cacheSize
  positive := input.positiveCapacity
  threshold := 1
  threshold_pos := zero_lt_one
  input := input
  size := rfl

/-- **The main theorem.**  Threshold-one FIFO is `(2k+2)`-competitive with no
additive constant: `ALG = 2M` and `M ≤ (k+1)·(S + D) = (k+1)·OPT`. -/
theorem competitiveRatio (input : Instance Page) :
    ∀ comparator : Schedule Page, comparator.Feasible input →
      (FIFO.schedule 1 input).totalCost input ≤
        (2 * input.cacheSize + 2 : ℕ) * comparator.totalCost input := by
  intro comparator feasible
  have hM := paymentCount_le (S := setupOne input) feasible
  have hcost := FIFO.algorithmCostClaim 1 input
  unfold FIFO.AlgorithmCostClaim FIFO.algorithmCost at hcost
  rw [hcost]
  have hcount : (FIFO.paymentCount 1 input : Cost) = ((setupOne input).count : Cost) := rfl
  rw [hcount]
  simp only [setupOne, div_one] at hM
  calc (1 + 1 : Cost) * ((setupOne input).count : Cost)
      ≤ (1 + 1 : Cost) * ((input.cacheSize + 1 : ℕ) * comparator.fetchCount +
          (input.cacheSize + 1 : ℕ) * comparator.totalDelay input) :=
        mul_le_mul_right hM _
    _ = (2 * input.cacheSize + 2 : ℕ) * comparator.totalCost input := by
        unfold Schedule.totalCost
        push_cast
        ring

end PagingWithDelay.RankPotential
