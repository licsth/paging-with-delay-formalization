import PagingWithDelay.KPlusOne.Hole
import PagingWithDelay.Analysis.Accrual
import PagingWithDelay.Competitive.DelayAccounting

/-!
# The amortized inequality of one interval

For every payment `i + 1` past the `k + 1`-st, the interval between payments
`i` and `i + 1` satisfies the paper's

  `k · Δ OPT + P(i+1) - P(i) ≥ 1`,

here written with the deficiency potential `Φ = rank (hole)` as

  `1 + Φ (i+1) ≤ k · Δ OPT + Φ i`.

The three cases of the paper appear as: the comparator holds the fetched page
at the end of the interval (`hole ≠ p`, a rank shift); it never holds it
(`hole = p` throughout, so its pending requests accrue the whole threshold);
or it dropped it during the interval (`hole = p` only at the end, which costs
the comparator an event, and two if it also started there).
-/

namespace PagingWithDelay.KPlusOne

open PagingWithDelay

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- The number of comparator events up to and including payment `i`. -/
def eventIndex (S : Setup Page) (comparator : Schedule Page) (i : ℕ) : ℕ :=
  Analysis.eventCount comparator (S.timeAt i)

/-- The comparator's hole immediately after payment `i`. -/
def holeAt (S : Setup Page) (comparator : Schedule Page) (i : ℕ) : Page :=
  hole S comparator (eventIndex S comparator i)

/-- The potential of the paper, in deficiency form.  With `k+1` pages FIFO's
cache is the universe minus the page it will fetch next, so the paper's
`∑_{q ∈ FIFO ∩ OPT} rank q`, read against the hole rather than against the
comparator's cache itself, is exactly `k(k+1)/2` minus this. -/
def potential (S : Setup Page) (comparator : Schedule Page) (i : ℕ) : ℕ :=
  Analysis.rank (S.queue (i + 1)) (holeAt S comparator i)

/-- The comparator's cost inside the interval `(t_i, t_{i+1}]`: the events it
makes there, plus the delay its requests accrue there. -/
def intervalCost (S : Setup Page) (comparator : Schedule Page) (i : ℕ) : Cost :=
  ((eventIndex S comparator (i + 1) - eventIndex S comparator i : ℕ) : Cost) +
    Analysis.delayIncrement comparator S.input (S.timeAt i) (S.timeAt (i + 1))

variable {S : Setup Page} {comparator : Schedule Page}

theorem eventIndex_monotone : Monotone (eventIndex S comparator) :=
  fun _ _ hij => Analysis.eventCount_mono comparator (S.timeAt_mono hij)

theorem eventCount_le_intervalCost (i : ℕ) :
    ((eventIndex S comparator (i + 1) - eventIndex S comparator i : ℕ) : Cost) ≤
      intervalCost S comparator i := by
  unfold intervalCost
  exact le_add_of_nonneg_right (zero_le _)

/-! ### The comparator does not serve a batch it never holds the page for -/

theorem no_early_service (feasible : comparator.Feasible S.input)
    {i : ℕ} (hfull : S.cacheSize ≤ i) (hi : i + 1 < S.count)
    (hcase : ∀ m, eventIndex S comparator i ≤ m → m ≤ eventIndex S comparator (i + 1) →
      hole S comparator m = S.pageAt (i + 1))
    {occurrence : Occurrence Page} (ho : occurrence ∈ (S.payments[i + 1]).served)
    {time : Time} (hmem : time ∈ comparator.serviceTime occurrence.request) :
    S.timeAt (i + 1) ≤ time := by
  have hpage : occurrence.request.page = S.pageAt (i + 1) :=
    S.served_page hi ho
  have hafter : S.timeAt i < occurrence.request.arrival := by
    have := S.served_arrival_gt (i := i + 1) (by omega) hi ho
    simpa using this
  have hbefore : occurrence.request.arrival ≤ S.timeAt (i + 1) :=
    S.served_arrival_le hi ho
  -- the comparator does not hold the page when the request arrives
  have hnothit : occurrence.request.page ∉
      comparator.cacheBefore occurrence.request.arrival := by
    rw [Analysis.cacheBefore_eq_cacheAfterCount feasible.chronological]
    set m := Analysis.eventCountLT comparator occurrence.request.arrival with hm
    have hlow : eventIndex S comparator i ≤ m :=
      Analysis.eventCount_le_eventCountLT comparator hafter
    have hhigh : m ≤ eventIndex S comparator (i + 1) :=
      Analysis.eventCountLT_le_eventCount comparator hbefore
    rw [hpage, ← hcase m hlow hhigh]
    exact hole_notMem_cache feasible m
  -- hence the only service candidates are fetches of the page
  have hcandidate : time ∈ comparator.serviceCandidates occurrence.request := by
    rw [Option.mem_def, Schedule.serviceTime] at hmem
    split at hmem
    · rename_i hnonempty
      have heq : (comparator.serviceCandidates occurrence.request).min' hnonempty = time :=
        Option.some_inj.mp hmem
      rw [← heq]
      exact Finset.min'_mem _ hnonempty
    · exact absurd hmem.symm (Option.some_ne_none time)
  rw [Schedule.serviceCandidates, if_neg hnothit, List.mem_toFinset, List.mem_map] at hcandidate
  obtain ⟨event, hevent, htime⟩ := hcandidate
  rw [List.mem_filter] at hevent
  obtain ⟨hmemEvent, hcond⟩ := hevent
  simp only [decide_eq_true_eq] at hcond
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn, hgetElem⟩ := List.mem_iff_getElem.mp hmemEvent
  have hntime : comparator.events[n].time = time := by rw [hgetElem]; exact htime
  have hupper : n < eventIndex S comparator (i + 1) := by
    refine Analysis.lt_eventCount_of_time_le feasible.chronological hn ?_
    rw [hntime]
    exact le_of_lt hlt
  have hlower : eventIndex S comparator i ≤ n := by
    by_contra hcontra
    push_neg at hcontra
    have hle := Analysis.time_le_of_lt_eventCount feasible.chronological hn hcontra
    rw [hntime] at hle
    have hgt : S.timeAt i < time := lt_of_lt_of_le hafter (htime ▸ hcond.1)
    exact absurd hle (not_le.mpr hgt)
  have hhole := hcase (n + 1) (by omega) (by omega)
  apply hole_notMem_cache feasible (n + 1)
  rw [hhole, ← hpage, hcond.2, ← hgetElem]
  exact Analysis.fetched_mem_cacheAfterCount comparator feasible.validTransitions hn

/-! ### The delay accrued by a batch the comparator never serves -/

theorem threshold_le_delayIncrement (feasible : comparator.Feasible S.input)
    {i : ℕ} (hfull : S.cacheSize ≤ i) (hi : i + 1 < S.count)
    (hcase : ∀ m, eventIndex S comparator i ≤ m → m ≤ eventIndex S comparator (i + 1) →
      hole S comparator m = S.pageAt (i + 1)) :
    S.threshold ≤
      Analysis.delayIncrement comparator S.input (S.timeAt i) (S.timeAt (i + 1)) := by
  classical
  set batch := (S.payments[i + 1]).served with hbatch
  set weight : ℕ → Cost := fun n =>
    Analysis.accruedAt comparator S.input n (S.timeAt (i + 1)) -
      Analysis.accruedAt comparator S.input n (S.timeAt i) with hweight
  -- identifiers of one batch are distinct
  have hnodup : (batch.map Occurrence.id).Nodup := by
    have hall : ((S.payments.flatMap FIFO.Payment.served).map Occurrence.id).Nodup :=
      FIFO.History.final_servedIds_nodup (δ := S.threshold) S.input
    have hmemPayment : S.payments[i + 1] ∈ S.payments :=
      List.getElem_mem (by simpa [Setup.count] using hi)
    have hsub : List.Sublist batch (S.payments.flatMap FIFO.Payment.served) := by
      rw [List.flatMap_def]
      exact List.sublist_flatten_of_mem (List.mem_map_of_mem hmemPayment)
    exact hall.sublist (hsub.map Occurrence.id)
  -- every identifier is an index into the request list
  have hids : (batch.map Occurrence.id).toFinset ⊆
      Finset.range S.input.requests.length := by
    intro n hn
    rw [List.mem_toFinset, List.mem_map] at hn
    obtain ⟨occurrence, ho, rfl⟩ := hn
    exact Finset.mem_range.mpr
      (Competitive.Schedule.id_lt_of_mem_enumerate (S.served_authentic hi ho))
  -- each served request accrues its full delay inside the interval
  have hterm : ∀ occurrence ∈ batch, weight occurrence.id =
      occurrence.request.delay (S.timeAt (i + 1) - occurrence.request.arrival) := by
    intro occurrence ho
    obtain ⟨hid, hrequest⟩ :=
      Competitive.Schedule.mem_enumerate_id_index (S.served_authentic hi ho)
    have hat : ∀ t : Time, Analysis.accruedAt comparator S.input occurrence.id t =
        Analysis.accruedCost comparator occurrence.request t := by
      intro t
      unfold Analysis.accruedAt
      rw [List.getElem?_eq_getElem hid, hrequest]
      rfl
    have hafter : S.timeAt i < occurrence.request.arrival := by
      have := S.served_arrival_gt (i := i + 1) (by omega) hi ho
      simpa using this
    rw [hweight]
    simp only [hat]
    rw [Analysis.accruedCost_eq_zero (le_of_lt hafter), tsub_zero,
      Analysis.accruedCost_eq_of_le_serviceTime
        (fun time hmem => no_early_service feasible hfull hi hcase ho hmem)]
  have hsum : ∑ n ∈ (batch.map Occurrence.id).toFinset, weight n = S.threshold := by
    rw [List.sum_toFinset weight hnodup, List.map_map]
    have : (batch.map (weight ∘ Occurrence.id)) =
        batch.map fun occurrence =>
          occurrence.request.delay (S.timeAt (i + 1) - occurrence.request.arrival) := by
      apply List.map_congr_left
      intro occurrence ho
      exact hterm occurrence ho
    rw [this]
    have hcost := S.payment_delayCost hi
    rw [FIFO.Payment.delayCost] at hcost
    rw [S.timeAt_eq hi]
    exact hcost
  rw [← hsum]
  exact Analysis.sum_le_delayIncrement comparator S.input _ _ hids

/-! ### The interval inequality -/

theorem interval_bound (feasible : comparator.Feasible S.input)
    {i : ℕ} (hfull : S.cacheSize ≤ i) (hi : i + 1 < S.count) :
    (1 : Cost) + (potential S comparator (i + 1) : Cost) ≤
      (S.cacheSize : Cost) * intervalCost S comparator i +
        (potential S comparator i : Cost) := by
  classical
  set F := eventIndex S comparator (i + 1) - eventIndex S comparator i with hF
  set p := S.pageAt (i + 1) with hp
  set Q := S.queue (i + 1) with hQ
  have hQlen : Q.length = S.cacheSize := by
    rw [hQ, S.queue_length (le_of_lt (by omega : i + 1 < S.count))]
    omega
  have hQnodup : Q.Nodup := S.queue_nodup (le_of_lt (by omega : i + 1 < S.count))
  have hpQ : p ∉ Q := S.pageAt_not_mem_queue (by omega)
  have hsucc : S.queue (i + 1 + 1) = Q.tail ++ [p] :=
    S.queue_succ_full (by omega) hi
  -- the hole is either the fetched page or a page of the cache
  have hholeQ : ∀ n : ℕ, hole S comparator n ≠ p → hole S comparator n ∈ Q := by
    intro n hne
    by_contra hnot
    exact hne (S.eq_pageAt_of_not_mem_queue (by omega) (by omega)
      (hole_mem_pages feasible n) hnot)
  -- the ℕ-valued inequality, in every case but the one paid by delay
  have hcount : ∀ hyp : (1 : ℕ) + potential S comparator (i + 1) ≤
      S.cacheSize * F + potential S comparator i,
      (1 : Cost) + (potential S comparator (i + 1) : Cost) ≤
        (S.cacheSize : Cost) * intervalCost S comparator i +
          (potential S comparator i : Cost) := by
    intro hyp
    have hcast : (1 : Cost) + (potential S comparator (i + 1) : Cost) ≤
        (S.cacheSize : Cost) * (F : Cost) + (potential S comparator i : Cost) := by
      exact_mod_cast hyp
    refine hcast.trans (add_le_add_left ?_ _)
    exact mul_le_mul_right (eventCount_le_intervalCost i) _
  by_cases hend : holeAt S comparator (i + 1) = p
  · -- the comparator does not hold the fetched page at the end of the interval
    have hphi : potential S comparator (i + 1) = S.cacheSize := by
      unfold potential
      rw [hsucc, hend, Analysis.rank_append_self (fun hcontra => hpQ (List.mem_of_mem_tail hcontra))]
      rw [List.length_tail, hQlen]
      exact Nat.succ_pred_eq_of_pos S.positive
    by_cases hall : ∀ m, eventIndex S comparator i ≤ m →
        m ≤ eventIndex S comparator (i + 1) → hole S comparator m = p
    · -- it never held it: its pending requests accrue the whole threshold
      have hdelay := threshold_le_delayIncrement feasible hfull hi hall
      have hmul : ((S.cacheSize : Cost) + 1) ≤
          (S.cacheSize : Cost) * intervalCost S comparator i := by
        calc ((S.cacheSize : Cost) + 1) = (S.cacheSize : Cost) * S.threshold :=
              (S.cacheSize_mul_threshold).symm
          _ ≤ (S.cacheSize : Cost) *
              Analysis.delayIncrement comparator S.input (S.timeAt i) (S.timeAt (i + 1)) :=
              mul_le_mul_right hdelay _
          _ ≤ (S.cacheSize : Cost) * intervalCost S comparator i := by
              refine mul_le_mul_right ?_ _
              unfold intervalCost
              exact le_add_of_nonneg_left (zero_le _)
      rw [hphi]
      calc (1 : Cost) + (S.cacheSize : Cost) = (S.cacheSize : Cost) + 1 := by ring
        _ ≤ (S.cacheSize : Cost) * intervalCost S comparator i := hmul
        _ ≤ _ := le_add_of_nonneg_right (zero_le _)
    · -- it dropped it during the interval, which costs it events
      push_neg at hall
      obtain ⟨m, hm1, hm2, hmne⟩ := hall
      refine hcount ?_
      rw [hphi]
      by_cases hstart : holeAt S comparator i = p
      · -- it started the interval without the page: two events
        have hne1 : m ≠ eventIndex S comparator i := by
          intro heq; exact hmne (heq ▸ hstart)
        have hne2 : m ≠ eventIndex S comparator (i + 1) := by
          intro heq; exact hmne (heq ▸ hend)
        have hFge : 2 ≤ F := by
          rw [hF]; omega
        have hk := S.positive
        calc 1 + S.cacheSize ≤ S.cacheSize * 2 := by omega
          _ ≤ S.cacheSize * F := Nat.mul_le_mul_left _ hFge
          _ ≤ S.cacheSize * F + potential S comparator i := Nat.le_add_right _ _
      · -- it started with the page: one event, and the potential is positive
        have hpos : 1 ≤ potential S comparator i := by
          unfold potential
          exact Analysis.one_le_rank_of_mem (hholeQ _ hstart)
        have hFge : 1 ≤ F := by
          rw [hF]
          by_contra hcontra
          push_neg at hcontra
          have heq : eventIndex S comparator i = eventIndex S comparator (i + 1) := by
            have : eventIndex S comparator i ≤ eventIndex S comparator (i + 1) :=
            eventIndex_monotone (Nat.le_succ i)
            omega
          exact hstart (by unfold holeAt; rw [heq]; exact hend)
        calc 1 + S.cacheSize ≤ S.cacheSize * F + 1 := by
              have := Nat.mul_le_mul_left S.cacheSize hFge
              omega
          _ ≤ S.cacheSize * F + potential S comparator i := by omega
  · -- the comparator holds the fetched page: FIFO's own step lifts the potential
    refine hcount ?_
    have hmemQ : holeAt S comparator (i + 1) ∈ Q := hholeQ _ hend
    have hshift : potential S comparator (i + 1) + 1 =
        Analysis.rank Q (holeAt S comparator (i + 1)) := by
      unfold potential
      rw [hsucc]
      exact Analysis.rank_shift hQnodup hmemQ hend
    have hle : Analysis.rank Q (holeAt S comparator (i + 1)) ≤
        S.cacheSize * F + potential S comparator i := by
      rcases Nat.eq_zero_or_pos F with hzero | hpos
      · have heq : eventIndex S comparator i = eventIndex S comparator (i + 1) := by
          have : eventIndex S comparator i ≤ eventIndex S comparator (i + 1) :=
            eventIndex_monotone (Nat.le_succ i)
          rw [hF] at hzero
          omega
        have : holeAt S comparator (i + 1) = holeAt S comparator i := by
          unfold holeAt; rw [heq]
        rw [this]
        exact Nat.le_add_left _ _
      · have hrank : Analysis.rank Q (holeAt S comparator (i + 1)) ≤ S.cacheSize := by
          rw [← hQlen]; exact Analysis.rank_le_length Q _
        calc Analysis.rank Q (holeAt S comparator (i + 1)) ≤ S.cacheSize := hrank
          _ ≤ S.cacheSize * F := Nat.le_mul_of_pos_right _ hpos
          _ ≤ S.cacheSize * F + potential S comparator i := Nat.le_add_right _ _
    calc 1 + potential S comparator (i + 1)
        = Analysis.rank Q (holeAt S comparator (i + 1)) := by
          rw [Nat.add_comm]; exact hshift
      _ ≤ S.cacheSize * F + potential S comparator i := hle

end

end PagingWithDelay.KPlusOne
