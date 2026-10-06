import Proofs.LowerBound.Steps

/-!
# FIFO faults on every request of the adversarial instance

The replay of `FIFO.run` on `input δ k runs pages hk`.  Between two consecutive
requests the event loop passes through a *settled* state: nothing is pending,
`i` requests have arrived and `i` fetches have been made.  Away from the
transposed pair of a run the loop moves from one settled state to the next in
two steps — an arrival, then the threshold crossing it causes (`beat_step`) —
and at the transposed pair in four (`transposed_beat`).
-/

namespace PagingWithDelay.LowerBound

open PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- A replay state: `i` fetches made, the first `j` requests arrived, and `pend` pending. -/
structure ReplayState (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) (i j : ℕ)
    (pend : List (Occurrence Page)) (state : State Page) : Prop where
  queue : state.queue = queueAt k pages i
  unseen : state.unseen = unseenFrom δ k runs pages j
  pending : state.pending = pend
  payments : state.payments.length = i

/-- The replay state after `i` arrivals and the `i` fetches they caused. -/
abbrev Settled (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) (i : ℕ) :
    State Page → Prop :=
  ReplayState δ k runs pages i i []

theorem settled_initial (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) {hk : 0 < k} :
    Settled δ k runs pages 0 (initialState (input δ k runs pages hk)) where
  queue := by simp [initialState, queueAt_zero]
  unseen := unseenFrom_zero δ k runs pages hk
  pending := rfl
  payments := rfl

omit [DecidableEq Page] in
/-- The occurrence at the head of the unseen list, identified. -/
theorem unseen_head_eq {δ : Cost} {k runs : ℕ} {pages : Fin (k + 2) ↪ Page} {j : ℕ}
    {occ : Occurrence Page} {rest : List (Occurrence Page)}
    (h : unseenFrom δ k runs pages j = occ :: rest) : occ = occAt δ k runs pages j := by
  rcases Nat.lt_or_ge j (runLength k * runs) with hj | hj
  · rw [unseenFrom_cons δ k runs pages hj] at h
    exact (List.cons_eq_cons.mp h).1.symm
  · rw [unseenFrom_nil δ k runs pages hj] at h
    exact absurd h (by simp)

section Steps

variable {δ : Cost} {k runs : ℕ} {hk : 0 < k} {pages : Fin (k + 2) ↪ Page} {i j : ℕ}
  {pend : List (Occurrence Page)} {state : State Page}

/-- The arrival of request `j`, whose page is not cached, makes it pending. -/
theorem ReplayState.arrive (hs : ReplayState δ k runs pages i j pend state)
    (hmiss : page k pages (pageCode k j) ∉ queueAt k pages i) :
    ReplayState δ k runs pages i (j + 1) (pend ++ [occAt δ k runs pages j])
      (step (input δ k runs pages hk) state (.arrival (occAt δ k runs pages j))) where
  queue := hs.queue
  unseen := (congrArg List.tail hs.unseen).trans (unseenFrom_tail δ k runs pages j)
  pending := by simp only [step, occAt_page, hs.queue, hs.pending, if_neg hmiss]
  payments := hs.payments

/-- A payment fetches the next page of the eviction order. -/
theorem ReplayState.pay (hs : ReplayState δ k runs pages i j pend state) {t : Time} {p : Page}
    (hp : p = fetchedPage k pages (i + 1)) {pend' : List (Occurrence Page)}
    (hpend : pend.filter (fun o => o.request.page ≠ p) = pend') :
    ReplayState δ k runs pages (i + 1) j pend'
      (step (input δ k runs pages hk) state (.payment t p)) where
  queue := by subst hp; rw [← queueAt_succ k hk pages i, ← hs.queue]; rfl
  unseen := hs.unseen
  pending := by simp only [step, hs.pending, hpend]
  payments := by simp [step, hs.payments]

/-- With nothing pending, the next request arrives. -/
theorem Settled.nextAction (hs : Settled δ k runs pages i state)
    (hi : i < runLength k * runs) :
    nextAction? (.threshold δ) state = some (.arrival (occAt δ k runs pages i)) :=
  nextAction_arrival (hs.unseen.trans (unseenFrom_cons δ k runs pages hi))
    (nextPayment_none hs.pending)

/-- A page whose only pending request is `m` reaches the threshold at `critTime k m`. -/
theorem thresholdTime_occAt (hδ : 0 < δ) {m : ℕ}
    (hfilter : (state.pending.filter fun o => o.request.page = page k pages (pageCode k m)) =
      [occAt δ k runs pages m])
    (hnow : state.now ≤ critTime k m) :
    thresholdTime δ state (page k pages (pageCode k m)) = critTime k m :=
  thresholdTime_single hδ state _ _ _ _ (width_pos k m) (width_le_horizon k runs m) hfilter rfl
    hnow

theorem nextPayment_occAt (hδ : 0 < δ) {m : ℕ} (hpend : state.pending = [occAt δ k runs pages m])
    (hnow : state.now ≤ critTime k m) :
    nextPayment? (.threshold δ) state = some (critTime k m, page k pages (pageCode k m)) := by
  rw [nextPayment_single hpend, occAt_page,
    thresholdTime_occAt (runs := runs) hδ (by simp [hpend]) hnow]

/-- Of two pending pages, the one reaching the threshold first is paid first. -/
theorem nextPayment_pair_occAt (hδ : 0 < δ) {m m' : ℕ}
    (hpend : state.pending = [occAt δ k runs pages m, occAt δ k runs pages m'])
    (hne : page k pages (pageCode k m) ≠ page k pages (pageCode k m'))
    (hnow : state.now ≤ critTime k m') (hlt : critTime k m' < critTime k m) :
    nextPayment? (.threshold δ) state = some (critTime k m', page k pages (pageCode k m')) := by
  have hthr := thresholdTime_occAt (runs := runs) (pages := pages) (m := m') hδ
    (by simp [hpend, hne]) hnow
  have hthr' := thresholdTime_occAt (runs := runs) (pages := pages) (m := m) hδ
    (by simp [hpend, Ne.symm hne]) (hnow.trans hlt.le)
  simpa only [occAt_page, hthr] using nextPayment_pair (δ := δ) hpend (by simpa using hne)
    (by simpa only [occAt_page, hthr, hthr'] using hlt)

/-- A payment due strictly before the next arrival is the next action. -/
theorem nextAction_pay {m : ℕ} {p : Page}
    (hp : nextPayment? (.threshold δ) state = some (critTime k m, p))
    (hu : state.unseen = unseenFrom δ k runs pages j)
    (hlt : critQuarters k m < arrivalQuarters k j) :
    nextAction? (.threshold δ) state = some (.payment (critTime k m) p) :=
  nextAction_payment hp fun occ rest hocc => by
    rw [hu] at hocc
    rw [unseen_head_eq hocc, occAt_arrival, critTime_eq, arrivalTime_eq]
    exact quarter_lt hlt

end Steps

/-- **A beat.**  From a settled state, one arrival and the fetch it triggers
lead to the next settled state. -/
theorem beat_step {δ : Cost} (hδ : 0 < δ) {k runs : ℕ} (hk : 0 < k)
    (pages : Fin (k + 2) ↪ Page) {i : ℕ} (hiN : i < runLength k * runs)
    (hfetch : pageCode k i = fetchedCode k (i + 1))
    (hmiss : page k pages (pageCode k i) ∉ queueAt k pages i)
    (hlt : critQuarters k i < arrivalQuarters k (i + 1))
    {state : State Page} (hs : Settled δ k runs pages i state) :
    Settled δ k runs pages (i + 1) (run (.threshold δ) (input δ k runs pages hk) 2 state) := by
  have h1 : ReplayState δ k runs pages i (i + 1) [occAt δ k runs pages i] _ :=
    hs.arrive (hk := hk) hmiss
  rw [run_step _ _ (hs.nextAction hiN),
    run_step _ _ (nextAction_pay (nextPayment_occAt hδ h1.pending le_self_add) h1.unseen hlt),
    run_zero]
  exact h1.pay (by rw [hfetch]; rfl) (by simp)

/-- **The transposed beat.**  At the pair of a run whose arrival order and
criticality order disagree, two arrivals precede the two fetches they cause,
and the fetches happen in the opposite order. -/
theorem transposed_beat {δ : Cost} (hδ : 0 < δ) {k runs : ℕ} (hk : 0 < k)
    (pages : Fin (k + 2) ↪ Page) {i : ℕ} (hiN : i + 1 < runLength k * runs)
    (hfetchC : pageCode k i = fetchedCode k (i + 2))
    (hfetchB : pageCode k (i + 1) = fetchedCode k (i + 1))
    (hne : page k pages (pageCode k i) ≠ page k pages (pageCode k (i + 1)))
    (hmissC : page k pages (pageCode k i) ∉ queueAt k pages i)
    (hmissB : page k pages (pageCode k (i + 1)) ∉ queueAt k pages i)
    (harrB : arrivalQuarters k (i + 1) ≤ critQuarters k i)
    (hcritB : critQuarters k (i + 1) < critQuarters k i)
    (hnextB : critQuarters k (i + 1) < arrivalQuarters k (i + 2))
    (hnextC : critQuarters k i < arrivalQuarters k (i + 2))
    {state : State Page} (hs : Settled δ k runs pages i state) :
    Settled δ k runs pages (i + 2) (run (.threshold δ) (input δ k runs pages hk) 4 state) := by
  have harrB' : arrivalTime k (i + 1) ≤ critTime k i := by
    rw [arrivalTime_eq, critTime_eq]; exact quarter_le harrB
  have hcritB' : critTime k (i + 1) < critTime k i := by
    rw [critTime_eq, critTime_eq]; exact quarter_lt hcritB
  -- the early request arrives, then the overtaking one before the first turns critical
  have h1 : ReplayState δ k runs pages i (i + 1) [occAt δ k runs pages i] _ :=
    hs.arrive (hk := hk) hmissC
  have hact2 := nextAction_arrival_of_le (h1.unseen.trans (unseenFrom_cons δ k runs pages hiN))
    (nextPayment_occAt hδ h1.pending le_self_add) harrB'
  have h2 : ReplayState δ k runs pages i (i + 2)
      [occAt δ k runs pages i, occAt δ k runs pages (i + 1)] _ := h1.arrive (hk := hk) hmissB
  -- the overtaking request turns critical first
  have hact3 := nextAction_pay (nextPayment_pair_occAt hδ h2.pending hne le_self_add hcritB')
    h2.unseen hnextB
  have h3 : ReplayState δ k runs pages (i + 1) (i + 2) [occAt δ k runs pages i] _ :=
    h2.pay (hk := hk) (t := critTime k (i + 1)) (p := page k pages (pageCode k (i + 1)))
      (by rw [hfetchB]; rfl) (by simp [hne])
  -- the early request turns critical last
  rw [run_step _ _ (hs.nextAction (by omega)), run_step _ _ hact2, run_step _ _ hact3,
    run_step _ _ (nextAction_pay (nextPayment_occAt hδ h3.pending hcritB'.le) h3.unseen hnextC),
    run_zero]
  exact h3.pay (by rw [hfetchC]; rfl) (by simp)

/-! ## The beats of the construction -/

omit [DecidableEq Page] in
/-- The page about to be fetched is never in the queue: it is entry `i + k` of
the eviction order, and the queue holds the `k` entries before it. -/
theorem notMem_queueAt_succ (k : ℕ) (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) (i : ℕ) :
    page k pages (fetchedCode k (i + 1)) ∉ queueAt k pages i := by
  refine notMem_queueAt hk (fetchedCode_lt k (i + 1) hk) ?_
  intro n hlo hhi
  have := entryCode_ne hk (n := n) (n' := i + k) (by omega) (by omega)
  rwa [entryCode_of_ge (show k ≤ i + k by omega), Nat.add_sub_cancel] at this

omit [DecidableEq Page] in
/-- The same for the early repeat request, which is fetched `k + 1` positions
after the request on `a` that still sits at the front of the queue. -/
theorem notMem_queueAt_early (k : ℕ) (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) (r : ℕ) :
    page k pages (fetchedCode k (runLength k * r + (k + 3))) ∉
      queueAt k pages (runLength k * r + (k + 1)) := by
  refine notMem_queueAt hk (fetchedCode_lt k _ hk) ?_
  intro n hlo hhi
  rw [entryCode_of_ge (show k ≤ n by omega)]
  rcases eq_or_lt_of_le hlo with heq | hlt
  · rw [← heq, show runLength k * r + (k + 1) - k + 1 = runLength k * r + 2 by omega]
    exact fetchedCode_a_ne k r hk
  · exact fetchedCode_ne hk (by omega) (by omega) (by omega)

theorem mod_ne_late (k r q : ℕ) (hk : 0 < k) (hq : q ≤ runLength k) (h : q ≠ k + 2) :
    (runLength k * r + q) % runLength k ≠ k + 2 := by
  have hL : runLength k = 2 * k + 2 := rfl
  rcases Nat.lt_or_ge q (runLength k) with hlt | hge
  · rw [mod_run k r q hlt]; exact h
  · have hqe : q = runLength k := by omega
    subst hqe
    rw [show runLength k * r + runLength k = runLength k * (r + 1) + 0 by ring,
      mod_run k (r + 1) 0 (runLength_pos k)]
    omega

/-- A beat at a position where arrival order and criticality order agree. -/
theorem beat_at {δ : Cost} (hδ : 0 < δ) {k runs : ℕ} (hk : 0 < k)
    (pages : Fin (k + 2) ↪ Page) {r q : ℕ} (hr : r < runs) (hq : q < runLength k)
    (h1 : q ≠ k + 1) (h2 : q ≠ k + 2) {state : State Page}
    (hs : Settled δ k runs pages (runLength k * r + q) state) :
    Settled δ k runs pages (runLength k * r + q + 1)
      (run (.threshold δ) (input δ k runs pages hk) 2 state) := by
  have hfetch := pageCode_generic k r q hq h1 h2
  have hc := critQuarters_generic k r q hq h1 h2
  have ha : 4 * (runLength k * r + q + 1) + 1 ≤ arrivalQuarters k (runLength k * r + q + 1) :=
    arrivalQuarters_lb k _ (mod_ne_late k r (q + 1) hk (by omega) (by omega))
  exact beat_step hδ hk pages (run_index_lt hr hq) hfetch
    (by rw [hfetch]; exact notMem_queueAt_succ k hk pages _) (by omega) hs

/-- The four-step beat at the transposed pair of a run. -/
theorem transposed_beat_at {δ : Cost} (hδ : 0 < δ) {k runs : ℕ} (hk : 0 < k)
    (pages : Fin (k + 2) ↪ Page) {r : ℕ} (hr : r < runs) {state : State Page}
    (hs : Settled δ k runs pages (runLength k * r + (k + 1)) state) :
    Settled δ k runs pages (runLength k * r + (k + 3))
      (run (.threshold δ) (input δ k runs pages hk) 4 state) := by
  have hL : runLength k = 2 * k + 2 := rfl
  have hcC := critQuarters_early k r hk
  have hcB := critQuarters_late k r hk
  have haB := arrivalQuarters_run k r (k + 2) (by omega)
  rw [if_neg (by omega), if_pos rfl] at haB
  have haNext := arrivalQuarters_lb k (runLength k * r + (k + 1) + 2)
    (mod_ne_late k r (k + 3) hk (by omega) (by omega))
  have e2 : runLength k * r + (k + 1) + 1 = runLength k * r + (k + 2) := rfl
  exact transposed_beat hδ hk pages (i := runLength k * r + (k + 1))
    (run_index_lt hr (q := k + 2) (by omega))
    (pageCode_early k r hk) (pageCode_late k r hk)
    (fun h => pageCode_early_ne_late k r hk
      (page_injOn pages (pageCode_lt k _ hk) (pageCode_lt k _ hk) h))
    (by rw [pageCode_early k r hk]; exact notMem_queueAt_early k hk pages r)
    (by rw [e2, pageCode_late k r hk]; exact notMem_queueAt_succ k hk pages _)
    (by rw [e2]; omega) (by rw [e2]; omega) (by rw [e2]; omega) (by omega) hs

/-! ## Chaining the beats -/

/-- A stretch of `n` beats from position `a` of a run, avoiding the transposed pair. -/
theorem chain {δ : Cost} (hδ : 0 < δ) {k runs : ℕ} (hk : 0 < k)
    (pages : Fin (k + 2) ↪ Page) {r a : ℕ} (hr : r < runs) {state : State Page}
    (hs : Settled δ k runs pages (runLength k * r + a) state) :
    ∀ n, a + n ≤ runLength k → (a + n ≤ k + 1 ∨ k + 3 ≤ a) →
      Settled δ k runs pages (runLength k * r + (a + n))
        (run (.threshold δ) (input δ k runs pages hk) (2 * n) state) := by
  intro n
  induction n with
  | zero => intro _ _; exact hs
  | succ n ih =>
      intro hn hgap
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, run_add]
      exact beat_at hδ hk pages hr (q := a + n) (by omega) (by omega) (by omega)
        (ih (by omega) (by omega))

/-- One whole run of the construction. -/
theorem run_beat {δ : Cost} (hδ : 0 < δ) {k runs : ℕ} (hk : 0 < k)
    (pages : Fin (k + 2) ↪ Page) {r : ℕ} (hr : r < runs) {state : State Page}
    (hs : Settled δ k runs pages (runLength k * r) state) :
    Settled δ k runs pages (runLength k * (r + 1))
      (run (.threshold δ) (input δ k runs pages hk) (2 * runLength k) state) := by
  have hL : runLength k = 2 * k + 2 := rfl
  have h1 := chain hδ hk pages hr (a := 0) hs (k + 1) (by omega) (by omega)
  rw [Nat.zero_add] at h1
  have h2 := transposed_beat_at hδ hk pages hr h1
  have h3 := chain hδ hk pages hr h2 (k - 1) (by omega) (by omega)
  have eidx : runLength k * (r + 1) = runLength k * r + (k + 3 + (k - 1)) := by
    have e : runLength k * (r + 1) = runLength k * r + runLength k := by ring
    omega
  rw [eidx, show 2 * runLength k = 2 * (k + 1) + 4 + 2 * (k - 1) by omega, run_add, run_add]
  exact h3

/-- The replay reaches a settled state at the start of every run. -/
theorem settled_runs {δ : Cost} (hδ : 0 < δ) {k runs : ℕ} (hk : 0 < k)
    (pages : Fin (k + 2) ↪ Page) : ∀ r ≤ runs,
      Settled δ k runs pages (runLength k * r)
        (run (.threshold δ) (input δ k runs pages hk) (2 * (runLength k * r))
          (initialState (input δ k runs pages hk))) := by
  intro r
  induction r with
  | zero => intro _; exact settled_initial δ k runs pages
  | succ r ih =>
      intro hr
      rw [show 2 * (runLength k * (r + 1)) = 2 * (runLength k * r) + 2 * runLength k by ring,
        run_add]
      exact run_beat hδ hk pages (by omega) (ih (by omega))

end
end PagingWithDelay.LowerBound
