import Proofs.LowerBound.CompSchedule

/-!
# What the comparator pays

Its `runs + 2` fetches are counted by `comparator_fetchCount`.  This file
settles the delay: every request except the one on `a` in each run is served
the moment it arrives, and each request on `a` waits on the comparator's plateau
and costs exactly the threshold `δ`.

The case analysis is by position `q` inside the run.  Writing `H` for the page
the comparator holds besides `v₁ … v_{k-1}`:

```text
q = 0        c        held (H)                       hit
q = 1        a        never held                     δ, served by the last fetch
2 ≤ q ≤ k    v        held throughout                hit
q = k+1      c        still held: the move is later  hit
q = k+2      b        the move happens now           served by that fetch
k+3 ≤ q      v        held throughout                hit
```
-/

namespace PagingWithDelay.LowerBound

open PagingWithDelay

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-! ## Two general facts about service -/

theorem arrival_le_of_mem_serviceCandidates (schedule : Schedule Page) (request : Request Page)
    {c : Time} (h : c ∈ schedule.serviceCandidates request) : request.arrival ≤ c := by
  unfold Schedule.serviceCandidates at h
  split at h <;> simp only [Finset.mem_insert, List.mem_toFinset, List.mem_map,
    List.mem_filter, decide_eq_true_eq] at h
  · rcases h with rfl | ⟨_, ⟨_, h, _⟩, rfl⟩
    exacts [le_rfl, h]
  · obtain ⟨_, ⟨_, h, _⟩, rfl⟩ := h
    exact h

/-- A request whose arrival is itself a service candidate costs nothing. -/
theorem requestCost_eq_zero_of_arrival_mem (schedule : Schedule Page) (request : Request Page)
    (h : request.arrival ∈ schedule.serviceCandidates request) :
    schedule.requestCost request = 0 := by
  rw [Schedule.requestCost_eq_of_serviceTime schedule request request.arrival
    (Schedule.serviceTime_eq_some_of_le_candidates schedule request request.arrival h
      fun c hc => arrival_le_of_mem_serviceCandidates schedule request hc)]
  simp [request.delay_zero]

theorem arrival_mem_serviceCandidates_of_hit (schedule : Schedule Page) (request : Request Page)
    (hhit : request.page ∈ schedule.cacheBefore request.arrival) :
    request.arrival ∈ schedule.serviceCandidates request := by
  simp [Schedule.serviceCandidates, hhit]

theorem mem_serviceCandidates_of_fetch (schedule : Schedule Page) (request : Request Page)
    {event : FetchEvent Page} (hevent : event ∈ schedule.events)
    (htime : request.arrival ≤ event.time) (hpage : request.page = event.fetched) :
    event.time ∈ schedule.serviceCandidates request := by
  unfold Schedule.serviceCandidates
  split <;> simp only [Finset.mem_insert, List.mem_toFinset, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  exacts [Or.inr ⟨event, ⟨hevent, htime, hpage⟩, rfl⟩, ⟨event, ⟨hevent, htime, hpage⟩, rfl⟩]

/-! ## Arrival times against the phase boundaries -/

theorem phaseQuarters_succ (k r : ℕ) :
    phaseQuarters k (r + 1) = 4 * (runLength k * r + (k + 2)) - 2 := by
  unfold phaseQuarters
  rw [if_neg (by omega), Nat.add_sub_cancel]

theorem phaseTime_succ (k r : ℕ) :
    phaseTime k (r + 1) = arrivalTime k (runLength k * r + (k + 2)) := by
  unfold phaseTime
  rw [if_neg (by omega), Nat.add_sub_cancel]

theorem phaseQuarters_lt_arrival (k r q : ℕ) (hk : 0 < k) (hq : q < runLength k) :
    phaseQuarters k r < arrivalQuarters k (runLength k * r + q) := by
  have hL : runLength k = 2 * k + 2 := rfl
  rw [arrivalQuarters_run k r q hq]
  rcases r with _ | r
  · simp only [phaseQuarters, if_pos]; split_ifs <;> omega
  · rw [phaseQuarters_succ, Nat.mul_succ]; split_ifs <;> omega

theorem arrivalQuarters_le_phaseQuarters_succ (k r q : ℕ) (hk : 0 < k) (hq : q ≤ k + 2) :
    arrivalQuarters k (runLength k * r + q) ≤ phaseQuarters k (r + 1) := by
  have hL : runLength k = 2 * k + 2 := rfl
  rw [phaseQuarters_succ, arrivalQuarters_run k r q (by omega)]
  split_ifs <;> omega

theorem phaseQuarters_succ_lt_arrival (k r q : ℕ) (hq1 : k + 3 ≤ q)
    (hq2 : q < runLength k) :
    phaseQuarters k (r + 1) < arrivalQuarters k (runLength k * r + q) := by
  have hL : runLength k = 2 * k + 2 := rfl
  rw [phaseQuarters_succ, arrivalQuarters_run k r q hq2]
  split_ifs <;> omega

theorem arrivalQuarters_le_phaseQuarters_succ_succ (k r q : ℕ) (hq : q < runLength k) :
    arrivalQuarters k (runLength k * r + q) ≤ phaseQuarters k (r + 2) := by
  have hL : runLength k = 2 * k + 2 := rfl
  have e : runLength k * (r + 1) = runLength k * r + runLength k := by ring
  have h := arrivalQuarters_le k (runLength k * r + q)
  rw [phaseQuarters_succ]
  omega

theorem arrivalQuarters_le_final (k r q runs : ℕ) (hr : r < runs) (hq : q < runLength k) :
    arrivalQuarters k (runLength k * r + q) ≤ 4 * (runLength k * runs) + 4 := by
  have h := arrivalQuarters_le k (runLength k * r + q)
  have := run_index_lt hr hq
  omega

/-! ## The comparator's cache when a request arrives -/

theorem cacheBefore_early {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) {runs r q : ℕ}
    (hr : r < runs) (hq : q ≤ k + 2) :
    (comparator k runs pages).cacheBefore (arrivalTime k (runLength k * r + q))
      = heldCache k pages (swapBC r 2) := by
  have hL : runLength k = 2 * k + 2 := rfl
  have hqL : q < runLength k := by omega
  refine comparator_cacheBefore pages (by omega) ?_ ?_ ?_
  · rw [phaseTime_eq k r hk, arrivalTime_eq]
    exact quarter_lt (phaseQuarters_lt_arrival k r q hk hqL)
  · intro r' hr' _
    rw [phaseTime_eq k r' hk, arrivalTime_eq]
    exact quarter_le ((arrivalQuarters_le_phaseQuarters_succ k r q hk hq).trans
      (phaseQuarters_mono k hr'))
  · rw [arrivalTime_eq, finalTime]
    exact quarter_le (arrivalQuarters_le_final k r q runs hr hqL)

theorem cacheBefore_late {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) {runs r q : ℕ}
    (hr : r < runs) (hq1 : k + 3 ≤ q) (hq2 : q < runLength k) :
    (comparator k runs pages).cacheBefore (arrivalTime k (runLength k * r + q))
      = heldCache k pages (swapBC (r + 1) 2) := by
  refine comparator_cacheBefore pages (by omega) ?_ ?_ ?_
  · rw [phaseTime_eq k (r + 1) hk, arrivalTime_eq]
    exact quarter_lt (phaseQuarters_succ_lt_arrival k r q hq1 hq2)
  · intro r' hr' _
    rw [phaseTime_eq k r' hk, arrivalTime_eq]
    exact quarter_le ((arrivalQuarters_le_phaseQuarters_succ_succ k r q hq2).trans
      (phaseQuarters_mono k hr'))
  · rw [arrivalTime_eq, finalTime]
    exact quarter_le (arrivalQuarters_le_final k r q runs hr hq2)

/-! ## Which page each request is on -/

theorem pageCode_held (k r q : ℕ) (hk : 0 < k) (h : q = 0 ∨ q = k + 1) :
    pageCode k (runLength k * r + q) = swapBC r 2 := by
  have hL : runLength k = 2 * k + 2 := rfl
  rw [pageCode_run k r q (by omega)]
  congr 1
  unfold critPos codeAt
  split_ifs <;> omega

theorem pageCode_a (k r : ℕ) (hk : 0 < k) : pageCode k (runLength k * r + 1) = 0 := by
  have hL : runLength k = 2 * k + 2 := rfl
  rw [pageCode_run k r 1 (by omega),
    show critPos k 1 = 2 by unfold critPos; split_ifs <;> omega,
    show codeAt k 2 = 0 by unfold codeAt; split_ifs <;> omega]
  unfold swapBC
  split_ifs <;> omega

theorem pageCode_moved (k r : ℕ) (hk : 0 < k) :
    pageCode k (runLength k * r + (k + 2)) = swapBC (r + 1) 2 := by
  rw [pageCode_run k r (k + 2) (by unfold runLength; omega),
    show critPos k (k + 2) = k + 2 by unfold critPos; split_ifs <;> omega,
    show codeAt k (k + 2) = 1 by unfold codeAt; split_ifs <;> omega, swapBC_one_eq]

theorem pageCode_v (k r q : ℕ) (hk : 0 < k) (hq : q < runLength k)
    (h : 2 ≤ q ∧ q ≤ k ∨ k + 3 ≤ q) : pageCode k (runLength k * r + q) ∈ vCodes k := by
  have hL : runLength k = 2 * k + 2 := rfl
  have hcode : 3 ≤ codeAt k (critPos k q) ∧ codeAt k (critPos k q) < k + 2 := by
    unfold critPos codeAt
    split_ifs <;> omega
  rw [pageCode_run k r q hq, mem_vCodes_iff,
    show swapBC r (codeAt k (critPos k q)) = codeAt k (critPos k q) by
      unfold swapBC; split_ifs <;> omega]
  omega

/-! ## Which event can serve a request -/

theorem phaseEvent_mem (k runs r : ℕ) (pages : Fin (k + 2) ↪ Page) (hr : r ≤ runs) :
    phaseEvent k pages r ∈ compEvents k runs pages := by
  simp only [compEvents, List.mem_append, List.mem_map, List.mem_range'_1]
  exact Or.inl ⟨r, ⟨Nat.zero_le _, by omega⟩, rfl⟩

theorem finalEvent_mem (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) :
    finalEvent k runs pages ∈ compEvents k runs pages := by
  simp [compEvents]

/-- Only the last fetch is on `a`. -/
theorem fetched_zero_time {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) (runs : ℕ)
    {event : FetchEvent Page} (hevent : event ∈ compEvents k runs pages)
    (hfetched : event.fetched = page k pages 0) : event.time = finalTime k runs := by
  simp only [compEvents, List.mem_append, List.mem_map, List.mem_singleton,
    List.mem_range'_1] at hevent
  rcases hevent with ⟨r, _, rfl⟩ | rfl
  · exact absurd (page_injOn pages (swapBC_two_lt k r hk) (show 0 < k + 2 by omega) hfetched)
      (swapBC_two_ne_zero r)
  · rfl

theorem serviceCandidate_eq_finalTime {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page)
    {runs : ℕ} {request : Request Page} (hpage : request.page = page k pages 0)
    (hmiss : request.page ∉ (comparator k runs pages).cacheBefore request.arrival)
    {c : Time} (hc : c ∈ (comparator k runs pages).serviceCandidates request) :
    c = finalTime k runs := by
  unfold Schedule.serviceCandidates at hc
  simp only [if_neg hmiss, List.mem_toFinset, List.mem_map, List.mem_filter,
    decide_eq_true_eq] at hc
  obtain ⟨event, ⟨hevent, -, hp⟩, rfl⟩ := hc
  exact fetched_zero_time hk pages runs hevent (hp.symm.trans hpage)

theorem page_mem_heldCache_of_vCodes {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page)
    {c d : ℕ} (h : c ∈ vCodes k) : page k pages c ∈ heldCache k pages d :=
  vSet_subset_heldCache pages d ((mem_vSet_iff hk pages (vCodes_lt k hk h)).mpr h)

theorem horizon_eq (k runs : ℕ) :
    horizon k runs = ((4 * (runLength k * runs) + 8 : ℕ) : Cost) / 4 := by
  unfold horizon
  push_cast
  ring

theorem quarter_sub {a b : ℕ} (h : b ≤ a) :
    ((a : Cost) / 4) - ((b : Cost) / 4) = (((a - b : ℕ) : Cost)) / 4 := by
  rw [tsub_eq_iff_eq_add_of_le (quarter_le h), ← add_div]
  congr 1
  rw [← Nat.cast_add, Nat.sub_add_cancel h]

/-! ## The cost of one request -/

/-- **Every request is served, and only the one on `a` costs anything.** -/
theorem comparator_serves {δ : Cost} {k : ℕ} (hk : 0 < k) {runs : ℕ}
    (pages : Fin (k + 2) ↪ Page) {r q : ℕ} (hr : r < runs) (hq : q < runLength k) :
    ((comparator k runs pages).serviceCandidates
        (requestAt δ k runs pages (runLength k * r + q))).Nonempty ∧
      (comparator k runs pages).requestCost (requestAt δ k runs pages (runLength k * r + q))
        = if q = 1 then δ else 0 := by
  have hL : runLength k = 2 * k + 2 := rfl
  have hmN := run_index_lt hr hq
  by_cases h1 : q = 1
  · subst h1
    -- the request on `a`, served by the comparator's last fetch
    have hpage : (requestAt δ k runs pages (runLength k * r + 1)).page = page k pages 0 :=
      congrArg (page k pages) (pageCode_a k r hk)
    have hmiss : (requestAt δ k runs pages (runLength k * r + 1)).page ∉
        (comparator k runs pages).cacheBefore (arrivalTime k (runLength k * r + 1)) := by
      rw [hpage, cacheBefore_early hk pages hr (by omega)]
      exact page_zero_notMem_heldCache hk pages _ (swapBC_two_lt k r hk) (swapBC_two_ne_zero r)
    have haq := arrivalQuarters_run k r 1 hq
    rw [if_neg (by omega), if_neg (by omega)] at haq
    have hle : arrivalQuarters k (runLength k * r + 1) ≤ 4 * (runLength k * runs) + 4 := by
      omega
    have hmem : finalTime k runs ∈ (comparator k runs pages).serviceCandidates
        (requestAt δ k runs pages (runLength k * r + 1)) :=
      mem_serviceCandidates_of_fetch _ _ (event := finalEvent k runs pages)
        (finalEvent_mem k runs pages) (quarter_le hle) hpage
    have hservice := Schedule.serviceTime_eq_some_of_le_candidates _ _ _ hmem
      fun c hc => (serviceCandidate_eq_finalTime hk pages hpage hmiss hc).ge
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [if_pos rfl, Schedule.requestCost_eq_of_serviceTime _ _ _ hservice]
    show curve δ 1 ((widthQuarters k (runLength k * r + 1) : Cost) / 4) (horizon k runs)
      (finalTime k runs - arrivalTime k (runLength k * r + 1)) = δ
    rw [arrivalTime_eq, finalTime, quarter_sub hle, horizon_eq, widthQuarters_run k r 1 hq,
      if_neg (by omega)]
    exact curve_eq_threshold _ _ _ _ (by norm_num) (quarter_le (by omega)) (quarter_le (by omega))
  · rw [if_neg h1]
    by_cases h2 : q = k + 2
    · subst h2
      -- the request on `b`: the comparator's fetch happens exactly now
      have harr : (requestAt δ k runs pages (runLength k * r + (k + 2))).arrival =
          (phaseEvent k pages (r + 1)).time := (phaseTime_succ k r).symm
      have hmem := mem_serviceCandidates_of_fetch (comparator k runs pages) _
        (phaseEvent_mem k runs (r + 1) pages (by omega)) harr.le
        (congrArg (page k pages) (pageCode_moved k r hk))
      rw [← harr] at hmem
      exact ⟨⟨_, hmem⟩, requestCost_eq_zero_of_arrival_mem _ _ hmem⟩
    · -- everything else is a hit
      have hhit : (requestAt δ k runs pages (runLength k * r + q)).page ∈
          (comparator k runs pages).cacheBefore (arrivalTime k (runLength k * r + q)) := by
        show page k pages (pageCode k (runLength k * r + q)) ∈ _
        rcases Nat.lt_or_ge q (k + 3) with hlt | hge
        · rw [cacheBefore_early hk pages hr (by omega)]
          by_cases hv : 2 ≤ q ∧ q ≤ k
          · exact page_mem_heldCache_of_vCodes hk pages (pageCode_v k r q hk hq (Or.inl hv))
          · rw [pageCode_held k r q hk (by omega)]
            exact Finset.mem_insert_self _ _
        · rw [cacheBefore_late hk pages hr hge hq]
          exact page_mem_heldCache_of_vCodes hk pages (pageCode_v k r q hk hq (Or.inr hge))
      exact ⟨⟨_, arrival_mem_serviceCandidates_of_hit _ _ hhit⟩,
        Schedule.requestCost_eq_zero_of_mem_cacheBefore _ _ hhit⟩

/-- `comparator_serves`, indexed by global arrival rank. -/
theorem comparator_serves_of_lt {δ : Cost} {k : ℕ} (hk : 0 < k) {runs : ℕ}
    (pages : Fin (k + 2) ↪ Page) {m : ℕ} (hm : m < runLength k * runs) :
    ((comparator k runs pages).serviceCandidates (requestAt δ k runs pages m)).Nonempty ∧
      (comparator k runs pages).requestCost (requestAt δ k runs pages m)
        = if m % runLength k = 1 then δ else 0 := by
  have h := comparator_serves (δ := δ) hk pages (Nat.div_lt_of_lt_mul hm)
    (Nat.mod_lt m (runLength_pos k))
  rwa [Nat.div_add_mod m (runLength k)] at h

/-! ## Summing over the instance -/

/-- One request per run pays, the one on `a`. -/
theorem sum_costs (δ : Cost) (k runs : ℕ) :
    ((List.range (runLength k * runs)).map
      (fun m => if m % runLength k = 1 then δ else 0)).sum = δ * runs := by
  have hL : 1 < runLength k := by unfold runLength; omega
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  induction runs with
  | zero => simp
  | succ runs ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih,
        Finset.sum_eq_single_of_mem 1 (Finset.mem_range.mpr hL)]
      · simp [Nat.mod_eq_of_lt hL, mul_add]
      · intro q hq hq1
        simp [Nat.mod_eq_of_lt (Finset.mem_range.mp hq), hq1]

theorem comparator_totalDelay {δ : Cost} {k : ℕ} (hk : 0 < k) {runs : ℕ}
    (pages : Fin (k + 2) ↪ Page) :
    (comparator k runs pages).totalDelay (input δ k runs pages hk) = δ * runs := by
  show (((List.range (runLength k * runs)).map (requestAt δ k runs pages)).map
    (comparator k runs pages).requestCost).sum = _
  rw [List.map_map, ← sum_costs δ k runs]
  exact congrArg List.sum (List.map_congr_left fun m hm =>
    (comparator_serves_of_lt hk pages (List.mem_range.mp hm)).2)

/-! ## The comparator of the paper -/

theorem comparator_feasible {δ : Cost} {k : ℕ} (hk : 0 < k) {runs : ℕ}
    (pages : Fin (k + 2) ↪ Page) :
    (comparator k runs pages).Feasible (input δ k runs pages hk) where
  initialCache := rfl
  chronological := comparator_chronological hk pages runs
  validTransitions := comparator_validTransitions hk pages runs
  capacity := comparator_capacity hk pages runs
  eventuallyServed := by
    intro request hrequest
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hrequest
    exact (comparator_serves_of_lt hk pages (List.mem_range.mp hm)).1

theorem comparator_totalCost {δ : Cost} {k : ℕ} (hk : 0 < k) {runs : ℕ}
    (pages : Fin (k + 2) ↪ Page) :
    (comparator k runs pages).totalCost (input δ k runs pages hk) = (1 + δ) * runs + 2 := by
  rw [Schedule.totalCost, comparator_fetchCount k runs pages, comparator_totalDelay hk pages]
  push_cast
  ring

end
end PagingWithDelay.LowerBound
