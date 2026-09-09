import PagingWithDelay.LowerBound.Steps

/-!
# FIFO faults on every request of the adversarial instance

The replay of `FIFO.run` on `input δ k runs pages`.  Between two consecutive
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

/-- The replay state after `i` arrivals and the `i` fetches they caused. -/
structure Settled (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) (i : ℕ)
    (state : State Page) : Prop where
  queue : state.queue = queueAt k pages i
  unseen : state.unseen = unseenFrom δ k runs pages i
  pending : state.pending = []
  payments : state.payments.length = i

theorem settled_initial (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) :
    Settled δ k runs pages 0 (initialState (input δ k runs pages)) where
  queue := by simp [initialState, queueAt]
  unseen := by
    show enumerate (input δ k runs pages).requests = _
    exact unseenFrom_zero δ k runs pages
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

/-- **A beat.**  From a settled state, one arrival and the fetch it triggers
lead to the next settled state. -/
theorem beat_step {δ : Cost} (hδ : 0 < δ) {k runs : ℕ} (hk : 0 < k)
    (pages : Fin (k + 2) ↪ Page) {i : ℕ} (hiN : i < runLength k * runs)
    (hfetch : pageCode k i = fetchedCode k (i + 1))
    (hmiss : page k pages (pageCode k i) ∉ queueAt k pages i)
    (hlt : critQuarters k i < arrivalQuarters k (i + 1))
    {state : State Page} (hs : Settled δ k runs pages i state) :
    Settled δ k runs pages (i + 1) (run δ (input δ k runs pages) 2 state) := by
  have hunseen : state.unseen =
      occAt δ k runs pages i :: unseenFrom δ k runs pages (i + 1) := by
    rw [hs.unseen, unseenFrom_cons δ k runs pages hiN]
  have hact1 : nextAction? δ state = some (Action.arrival (occAt δ k runs pages i)) :=
    nextAction_arrival hunseen (nextPayment_none hs.pending)
  rw [show (2 : ℕ) = 1 + 1 from rfl, run_step _ 1 hact1]
  set s1 := step (input δ k runs pages) state (Action.arrival (occAt δ k runs pages i))
    with hs1def
  have hs1queue : s1.queue = queueAt k pages i := by
    rw [hs1def]; simp only [step]; exact hs.queue
  have hs1unseen : s1.unseen = unseenFrom δ k runs pages (i + 1) := by
    rw [hs1def]; simp only [step]; rw [hunseen]; rfl
  have hs1pending : s1.pending = [occAt δ k runs pages i] := by
    rw [hs1def]; simp only [step, occAt_page, hs.queue, hs.pending, if_neg hmiss]; rfl
  have hs1now : s1.now = arrivalTime k i := by rw [hs1def]; simp only [step]; rfl
  have hs1payments : s1.payments = state.payments := by rw [hs1def]; simp only [step]
  have hthr : thresholdTime δ s1 (page k pages (pageCode k i)) = critTime k i := by
    refine thresholdTime_single hδ s1 _ (occAt δ k runs pages i) (width k i)
      (horizon k runs) (width_pos k i) (width_le_horizon k runs i) ?_ rfl ?_
    · rw [hs1pending]; simp
    · rw [hs1now]; exact le_self_add
  have hpay : nextPayment? δ s1 = some (critTime k i, page k pages (pageCode k i)) := by
    rw [nextPayment_single hs1pending]
    simp only [occAt_page, hthr]
  have hact2 : nextAction? δ s1 =
      some (Action.payment (critTime k i) (page k pages (pageCode k i))) := by
    refine nextAction_payment hpay ?_
    intro occ rest hocc
    rw [hs1unseen] at hocc
    rw [unseen_head_eq hocc, occAt_arrival, critTime_eq, arrivalTime_eq]
    exact quarter_lt hlt
  rw [run_step _ 0 hact2, run_zero]
  set s2 := step (input δ k runs pages) s1
    (Action.payment (critTime k i) (page k pages (pageCode k i))) with hs2def
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hs2def]
    simp only [step, input_cacheSize, hs1queue, hfetch]
    exact queueAt_succ k hk pages i
  · rw [hs2def]; simp only [step]; exact hs1unseen
  · rw [hs2def]; simp only [step, hs1pending]; simp
  · rw [hs2def]; simp only [step, hs1payments]; simp [hs.payments]

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
    Settled δ k runs pages (i + 2) (run δ (input δ k runs pages) 4 state) := by
  have hiN' : i < runLength k * runs := by omega
  -- step 1: the early request arrives
  have hunseen : state.unseen =
      occAt δ k runs pages i :: unseenFrom δ k runs pages (i + 1) := by
    rw [hs.unseen, unseenFrom_cons δ k runs pages hiN']
  have hact1 : nextAction? δ state = some (Action.arrival (occAt δ k runs pages i)) :=
    nextAction_arrival hunseen (nextPayment_none hs.pending)
  rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, run_step _ 3 hact1]
  set s1 := step (input δ k runs pages) state (Action.arrival (occAt δ k runs pages i))
    with hs1def
  have hs1queue : s1.queue = queueAt k pages i := by
    rw [hs1def]; simp only [step]; exact hs.queue
  have hs1unseen : s1.unseen = unseenFrom δ k runs pages (i + 1) := by
    rw [hs1def]; simp only [step]; rw [hunseen]; rfl
  have hs1pending : s1.pending = [occAt δ k runs pages i] := by
    rw [hs1def]; simp only [step, occAt_page, hs.queue, hs.pending, if_neg hmissC]; rfl
  have hs1now : s1.now = arrivalTime k i := by rw [hs1def]; simp only [step]; rfl
  have hs1payments : s1.payments = state.payments := by rw [hs1def]; simp only [step]
  -- step 2: the overtaking request arrives before the first one turns critical
  have hthr1 : thresholdTime δ s1 (page k pages (pageCode k i)) = critTime k i := by
    refine thresholdTime_single hδ s1 _ (occAt δ k runs pages i) (width k i)
      (horizon k runs) (width_pos k i) (width_le_horizon k runs i) ?_ rfl ?_
    · rw [hs1pending]; simp
    · rw [hs1now]; exact le_self_add
  have hpay1 : nextPayment? δ s1 = some (critTime k i, page k pages (pageCode k i)) := by
    rw [nextPayment_single hs1pending]; simp only [occAt_page, hthr1]
  have hs1cons : s1.unseen =
      occAt δ k runs pages (i + 1) :: unseenFrom δ k runs pages (i + 2) := by
    rw [hs1unseen, unseenFrom_cons δ k runs pages hiN]
  have hact2 : nextAction? δ s1 = some (Action.arrival (occAt δ k runs pages (i + 1))) := by
    refine nextAction_arrival_of_le hs1cons hpay1 ?_
    rw [occAt_arrival, critTime_eq, arrivalTime_eq]
    exact quarter_le harrB
  rw [run_step _ 2 hact2]
  set s2 := step (input δ k runs pages) s1 (Action.arrival (occAt δ k runs pages (i + 1)))
    with hs2def
  have hs2queue : s2.queue = queueAt k pages i := by
    rw [hs2def]; simp only [step]; exact hs1queue
  have hs2unseen : s2.unseen = unseenFrom δ k runs pages (i + 2) := by
    rw [hs2def]; simp only [step]; rw [hs1cons]; rfl
  have hs2pending : s2.pending =
      [occAt δ k runs pages i, occAt δ k runs pages (i + 1)] := by
    rw [hs2def]; simp only [step, occAt_page, hs1queue, hs1pending, if_neg hmissB]; rfl
  have hs2now : s2.now = arrivalTime k (i + 1) := by rw [hs2def]; simp only [step]; rfl
  have hs2payments : s2.payments = state.payments := by
    rw [hs2def]; simp only [step]; exact hs1payments
  -- step 3: the overtaking request turns critical first
  have hthr2C : thresholdTime δ s2 (page k pages (pageCode k i)) = critTime k i := by
    refine thresholdTime_single hδ s2 _ (occAt δ k runs pages i) (width k i)
      (horizon k runs) (width_pos k i) (width_le_horizon k runs i) ?_ rfl ?_
    · rw [hs2pending]; simp [Ne.symm hne]
    · rw [hs2now]
      show arrivalTime k (i + 1) ≤ critTime k i
      rw [arrivalTime_eq, critTime_eq]
      exact quarter_le harrB
  have hthr2B : thresholdTime δ s2 (page k pages (pageCode k (i + 1))) =
      critTime k (i + 1) := by
    refine thresholdTime_single hδ s2 _ (occAt δ k runs pages (i + 1)) (width k (i + 1))
      (horizon k runs) (width_pos k (i + 1)) (width_le_horizon k runs (i + 1)) ?_ rfl ?_
    · rw [hs2pending]; simp [hne]
    · rw [hs2now]; exact le_self_add
  have hpay2 : nextPayment? δ s2 =
      some (critTime k (i + 1), page k pages (pageCode k (i + 1))) := by
    have := nextPayment_pair (δ := δ) hs2pending (by simpa using hne)
      (by simp only [occAt_page, hthr2B, hthr2C, critTime_eq]; exact quarter_lt hcritB)
    simpa only [occAt_page, hthr2B] using this
  have hact3 : nextAction? δ s2 =
      some (Action.payment (critTime k (i + 1)) (page k pages (pageCode k (i + 1)))) := by
    refine nextAction_payment hpay2 ?_
    intro occ rest hocc
    rw [hs2unseen] at hocc
    rw [unseen_head_eq hocc, occAt_arrival, critTime_eq, arrivalTime_eq]
    exact quarter_lt hnextB
  rw [run_step _ 1 hact3]
  set s3 := step (input δ k runs pages) s2
    (Action.payment (critTime k (i + 1)) (page k pages (pageCode k (i + 1)))) with hs3def
  have hs3queue : s3.queue = queueAt k pages (i + 1) := by
    rw [hs3def]
    simp only [step, input_cacheSize, hs2queue, hfetchB]
    exact queueAt_succ k hk pages i
  have hs3unseen : s3.unseen = unseenFrom δ k runs pages (i + 2) := by
    rw [hs3def]; simp only [step]; exact hs2unseen
  have hs3pending : s3.pending = [occAt δ k runs pages i] := by
    rw [hs3def]; simp only [step, hs2pending]; simp [hne]
  have hs3now : s3.now = critTime k (i + 1) := by rw [hs3def]; simp only [step]
  have hs3payments : s3.payments.length = i + 1 := by
    rw [hs3def]; simp only [step, hs2payments]; simp [hs.payments]
  -- step 4: the early request turns critical last
  have hthr3 : thresholdTime δ s3 (page k pages (pageCode k i)) = critTime k i := by
    refine thresholdTime_single hδ s3 _ (occAt δ k runs pages i) (width k i)
      (horizon k runs) (width_pos k i) (width_le_horizon k runs i) ?_ rfl ?_
    · rw [hs3pending]; simp
    · rw [hs3now]
      show critTime k (i + 1) ≤ critTime k i
      rw [critTime_eq, critTime_eq]
      exact le_of_lt (quarter_lt hcritB)
  have hpay3 : nextPayment? δ s3 = some (critTime k i, page k pages (pageCode k i)) := by
    rw [nextPayment_single hs3pending]; simp only [occAt_page, hthr3]
  have hact4 : nextAction? δ s3 =
      some (Action.payment (critTime k i) (page k pages (pageCode k i))) := by
    refine nextAction_payment hpay3 ?_
    intro occ rest hocc
    rw [hs3unseen] at hocc
    rw [unseen_head_eq hocc, occAt_arrival, critTime_eq, arrivalTime_eq]
    exact quarter_lt hnextC
  rw [run_step _ 0 hact4, run_zero]
  set s4 := step (input δ k runs pages) s3
    (Action.payment (critTime k i) (page k pages (pageCode k i))) with hs4def
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hs4def]
    simp only [step, input_cacheSize, hs3queue, hfetchC]
    exact queueAt_succ k hk pages (i + 1)
  · rw [hs4def]; simp only [step]; exact hs3unseen
  · rw [hs4def]; simp only [step, hs3pending]; simp
  · rw [hs4def]; simp only [step]; simp [hs3payments]

/-! ## The beats of the construction -/

omit [DecidableEq Page] in
/-- The page about to be fetched is never in the queue: it was fetched, if at
all, more than `k` fetches ago. -/
theorem notMem_queueAt_succ (k : ℕ) (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) (i : ℕ) :
    page k pages (fetchedCode k (i + 1)) ∉ queueAt k pages i := by
  refine notMem_queueAt hk (fetchedCode_lt k (i + 1) hk) ?_
  intro j hlo hhi
  have h1 : min i k ≤ k := min_le_right i k
  have h2 : min i k ≤ i := min_le_left i k
  exact fetchedCode_ne hk (by omega) (by omega) (by omega)

omit [DecidableEq Page] in
/-- The same for the early repeat request, which is fetched `k + 1` positions
after the request on `a` that still sits at the front of the queue. -/
theorem notMem_queueAt_early (k : ℕ) (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) (r : ℕ) :
    page k pages (fetchedCode k (runLength k * r + (k + 3))) ∉
      queueAt k pages (runLength k * r + (k + 1)) := by
  have hmin : min (runLength k * r + (k + 1)) k = k := by omega
  refine notMem_queueAt hk (fetchedCode_lt k _ hk) ?_
  intro j hlo hhi
  rw [hmin] at hlo
  rcases eq_or_lt_of_le hlo with heq | hlt
  · rw [← heq, show runLength k * r + (k + 1) + 1 - k = runLength k * r + 2 by omega]
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
      (run δ (input δ k runs pages) 2 state) := by
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
      (run δ (input δ k runs pages) 4 state) := by
  have hL : runLength k = 2 * k + 2 := rfl
  have e2 : runLength k * r + (k + 1) + 1 = runLength k * r + (k + 2) := rfl
  have e3 : runLength k * r + (k + 1) + 2 = runLength k * r + (k + 3) := rfl
  have hiN : runLength k * r + (k + 1) + 1 < runLength k * runs := by
    rw [e2]; exact run_index_lt hr (by omega)
  have hcC : critQuarters k (runLength k * r + (k + 1)) =
      4 * (runLength k * r + (k + 1)) + 8 := critQuarters_early k r hk
  have hcB : critQuarters k (runLength k * r + (k + 1) + 1) =
      4 * (runLength k * r + (k + 2)) := by rw [e2]; exact critQuarters_late k r hk
  have haB : arrivalQuarters k (runLength k * r + (k + 1) + 1) =
      4 * (runLength k * r + (k + 2)) - 2 := by
    rw [e2, arrivalQuarters_run k r (k + 2) (by omega), if_neg (by omega), if_pos rfl]
  have haNext : 4 * (runLength k * r + (k + 3)) + 1 ≤
      arrivalQuarters k (runLength k * r + (k + 1) + 2) := by
    rw [e3]; exact arrivalQuarters_lb k _ (mod_ne_late k r (k + 3) hk (by omega) (by omega))
  have hres := transposed_beat hδ hk pages hiN
    (by rw [e3]; exact pageCode_early k r hk)
    (by rw [e2]; exact pageCode_late k r hk)
    (fun h => pageCode_early_ne_late k r hk
      (page_injOn pages (pageCode_lt k _ hk) (pageCode_lt k _ hk) h))
    (by rw [pageCode_early k r hk]; exact notMem_queueAt_early k hk pages r)
    (by rw [e2, pageCode_late k r hk]; exact notMem_queueAt_succ k hk pages _)
    (by omega) (by omega) (by omega) (by omega) hs
  rw [e3] at hres
  exact hres

/-! ## Chaining the beats -/

/-- The part of a run before the transposed pair. -/
theorem chain_pre {δ : Cost} (hδ : 0 < δ) {k runs : ℕ} (hk : 0 < k)
    (pages : Fin (k + 2) ↪ Page) {r : ℕ} (hr : r < runs) {state : State Page}
    (hs : Settled δ k runs pages (runLength k * r) state) :
    ∀ q ≤ k + 1, Settled δ k runs pages (runLength k * r + q)
      (run δ (input δ k runs pages) (2 * q) state) := by
  intro q
  induction q with
  | zero => intro _; rw [Nat.mul_zero, run_zero, Nat.add_zero]; exact hs
  | succ q ih =>
      intro hq
      have hprev := ih (by omega)
      have hstep := beat_at hδ hk pages hr (q := q) (by unfold runLength; omega)
        (by omega) (by omega) hprev
      rw [show 2 * (q + 1) = 2 * q + 2 by ring, run_add]
      exact hstep

/-- The part of a run after the transposed pair. -/
theorem chain_post {δ : Cost} (hδ : 0 < δ) {k runs : ℕ} (hk : 0 < k)
    (pages : Fin (k + 2) ↪ Page) {r : ℕ} (hr : r < runs) {state : State Page}
    (hs : Settled δ k runs pages (runLength k * r + (k + 3)) state) :
    ∀ n, k + 3 + n ≤ runLength k →
      Settled δ k runs pages (runLength k * r + (k + 3 + n))
        (run δ (input δ k runs pages) (2 * n) state) := by
  intro n
  induction n with
  | zero => intro _; rw [Nat.mul_zero, run_zero]; exact hs
  | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hstep := beat_at hδ hk pages hr (q := k + 3 + n) (by omega)
        (by omega) (by omega) hprev
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, run_add]
      exact hstep

/-- One whole run of the construction. -/
theorem run_beat {δ : Cost} (hδ : 0 < δ) {k runs : ℕ} (hk : 0 < k)
    (pages : Fin (k + 2) ↪ Page) {r : ℕ} (hr : r < runs) {state : State Page}
    (hs : Settled δ k runs pages (runLength k * r) state) :
    Settled δ k runs pages (runLength k * (r + 1))
      (run δ (input δ k runs pages) (2 * runLength k) state) := by
  have hL : runLength k = 2 * k + 2 := rfl
  have h1 := chain_pre hδ hk pages hr hs (k + 1) le_rfl
  have h2 := transposed_beat_at hδ hk pages hr h1
  have h3 := chain_post hδ hk pages hr h2 (k - 1) (by omega)
  have eidx : runLength k * (r + 1) = runLength k * r + (k + 3 + (k - 1)) := by
    have e : runLength k * (r + 1) = runLength k * r + runLength k := by ring
    omega
  rw [eidx, show 2 * runLength k = 2 * (k + 1) + 4 + 2 * (k - 1) by omega, run_add, run_add]
  exact h3

/-- The replay reaches a settled state at the start of every run. -/
theorem settled_runs {δ : Cost} (hδ : 0 < δ) {k runs : ℕ} (hk : 0 < k)
    (pages : Fin (k + 2) ↪ Page) : ∀ r ≤ runs,
      Settled δ k runs pages (runLength k * r)
        (run δ (input δ k runs pages) (2 * (runLength k * r))
          (initialState (input δ k runs pages))) := by
  intro r
  induction r with
  | zero =>
      intro _
      rw [Nat.mul_zero, Nat.mul_zero, run_zero]
      exact settled_initial δ k runs pages
  | succ r ih =>
      intro hr
      have hprev := ih (by omega)
      have hstep := run_beat hδ hk pages (show r < runs by omega) hprev
      rw [show 2 * (runLength k * (r + 1)) = 2 * (runLength k * r) + 2 * runLength k by ring,
        run_add]
      exact hstep

end
end PagingWithDelay.LowerBound
