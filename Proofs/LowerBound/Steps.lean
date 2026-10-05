import Proofs.LowerBound.Simulation

/-!
# One step of the event loop on the adversarial instance

Everything needed to read off a single `FIFO.step` of the replay: the times of
the instance compared in quarters, the threshold time of a page with exactly
one pending request, the two shapes of `nextAction?` that occur, and the
composition law for `FIFO.run`.
-/

namespace PagingWithDelay.LowerBound

open PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-! ## Times, in quarters -/

theorem quarter_le {a b : ℕ} (h : a ≤ b) : ((a : Cost) / 4) ≤ ((b : Cost) / 4) := by
  rw [← NNReal.coe_le_coe]
  push_cast
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  linarith

theorem quarter_lt {a b : ℕ} (h : a < b) : ((a : Cost) / 4) < ((b : Cost) / 4) := by
  rw [← NNReal.coe_lt_coe]
  push_cast
  have : (a : ℝ) < b := by exact_mod_cast h
  linarith

/-- Quarters after time zero at which the request with arrival rank `m` reaches
the threshold. -/
def critQuarters (k m : ℕ) : ℕ := arrivalQuarters k m + widthQuarters k m

theorem arrivalTime_eq (k m : ℕ) : arrivalTime k m = ((arrivalQuarters k m : Cost) / 4) := rfl

theorem critTime_eq (k m : ℕ) : critTime k m = ((critQuarters k m : Cost) / 4) := by
  unfold critTime arrivalTime width critQuarters
  push_cast
  ring

theorem arrivalQuarters_run (k r q : ℕ) (h : q < runLength k) :
    arrivalQuarters k (runLength k * r + q) =
      if q = k + 1 then 4 * (runLength k * r + q) + 1
      else if q = k + 2 then 4 * (runLength k * r + q) - 2
      else 4 * (runLength k * r + q) + 2 := by
  unfold arrivalQuarters
  rw [mod_run k r q h]

theorem widthQuarters_run (k r q : ℕ) (h : q < runLength k) :
    widthQuarters k (runLength k * r + q) = if q = k + 1 then 7 else 2 := by
  unfold widthQuarters
  rw [mod_run k r q h]

theorem critQuarters_generic (k r q : ℕ) (h : q < runLength k) (h1 : q ≠ k + 1)
    (h2 : q ≠ k + 2) :
    critQuarters k (runLength k * r + q) = 4 * (runLength k * r + q) + 4 := by
  unfold critQuarters
  rw [arrivalQuarters_run k r q h, widthQuarters_run k r q h, if_neg h1, if_neg h1, if_neg h2]

theorem critQuarters_early (k r : ℕ) (hk : 0 < k) :
    critQuarters k (runLength k * r + (k + 1)) = 4 * (runLength k * r + (k + 1)) + 8 := by
  have hL : runLength k = 2 * k + 2 := rfl
  unfold critQuarters
  rw [arrivalQuarters_run k r (k + 1) (by omega), widthQuarters_run k r (k + 1) (by omega),
    if_pos rfl, if_pos rfl]

theorem critQuarters_late (k r : ℕ) (hk : 0 < k) :
    critQuarters k (runLength k * r + (k + 2)) = 4 * (runLength k * r + (k + 2)) := by
  have hL : runLength k = 2 * k + 2 := rfl
  unfold critQuarters
  rw [arrivalQuarters_run k r (k + 2) (by omega), widthQuarters_run k r (k + 2) (by omega),
    if_neg (by omega), if_pos rfl, if_neg (by omega)]
  omega

/-- Every arrival happens at least a quarter after the last threshold crossing
that precedes it, unless it is the overtaken request on `b`. -/
theorem arrivalQuarters_lb (k m : ℕ) (h : m % runLength k ≠ k + 2) :
    4 * m + 1 ≤ arrivalQuarters k m := by
  unfold arrivalQuarters
  split_ifs <;> omega

/-! ## Occurrences of the instance -/

omit [DecidableEq Page] in
@[simp] theorem occAt_page (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) (m : ℕ) :
    (occAt δ k runs pages m).request.page = page k pages (pageCode k m) := rfl

omit [DecidableEq Page] in
@[simp] theorem occAt_arrival (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) (m : ℕ) :
    (occAt δ k runs pages m).request.arrival = arrivalTime k m := rfl

omit [DecidableEq Page] in
@[simp] theorem occAt_delay (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) (m : ℕ) :
    (occAt δ k runs pages m).request.delay = curve δ 1 (width k m) (horizon k runs) := rfl

/-! ## The threshold time of a single pending request -/

theorem curve_ge_threshold (δ η w B : Cost) (hw : 0 < w) {x : Time} (hx : w ≤ x) :
    δ ≤ curve δ η w B x := by
  rw [curve, min_eq_right ((one_le_div hw).mpr hx), mul_one]
  exact le_add_of_nonneg_right (zero_le _)

theorem le_tsub_iff_of_pos {a w t : Time} (hw : 0 < w) : w ≤ t - a ↔ a + w ≤ t := by
  rcases le_or_gt a t with h | h
  · rw [le_tsub_iff_right h, add_comm]
  · constructor
    · intro hle
      rw [tsub_eq_zero_of_le h.le] at hle
      exact absurd (le_antisymm hle (zero_le w)) hw.ne'
    · intro hle
      exact absurd (le_self_add.trans hle) (not_le.mpr h)

/-- When exactly one pending request is for `p`, the threshold is met exactly
at that request's own crossing time. -/
theorem thresholdTime_single {δ : Cost} (hδ : 0 < δ) (state : State Page) (p : Page)
    (occ : Occurrence Page) (w B : Cost) (hw : 0 < w) (hwB : w ≤ B)
    (hfilter : (state.pending.filter fun o => o.request.page = p) = [occ])
    (hdelay : occ.request.delay = curve δ 1 w B)
    (hnow : state.now ≤ occ.request.arrival + w) :
    thresholdTime δ state p = occ.request.arrival + w := by
  have hcost : ∀ t : Time, pendingCost state p t = curve δ 1 w B (t - occ.request.arrival) := by
    intro t
    unfold pendingCost
    rw [hfilter]
    simp [hdelay]
  have hset : {t : Time | state.now ≤ t ∧ δ ≤ pendingCost state p t}
      = Set.Ici (occ.request.arrival + w) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Ici, hcost]
    constructor
    · rintro ⟨-, h2⟩
      by_contra hcon
      rw [not_le] at hcon
      have hlt : t - occ.request.arrival < w := by
        rw [← not_le, le_tsub_iff_of_pos hw, not_le]
        exact hcon
      exact absurd h2 (not_le.mpr (curve_lt_threshold δ 1 w B hδ hwB hlt))
    · intro hle
      exact ⟨hnow.trans hle,
        curve_ge_threshold δ 1 w B hw ((le_tsub_iff_of_pos hw).mpr hle)⟩
  unfold thresholdTime
  rw [hset]
  exact csInf_Ici

/-! ## Selecting the next action -/

theorem nextPayment_none {δ : Cost} {state : State Page} (h : state.pending = []) :
    nextPayment? (.threshold δ) state = none := by
  simp [nextPayment?, pendingPages, h]

theorem nextPayment_single {δ : Cost} {state : State Page} {occ : Occurrence Page}
    (h : state.pending = [occ]) :
    nextPayment? (.threshold δ) state = some (thresholdTime δ state occ.request.page, occ.request.page) := by
  simp [nextPayment?, pendingPages, h, List.eraseDups, List.eraseDupsBy,
    List.eraseDupsBy.loop]

theorem nextPayment_pair {δ : Cost} {state : State Page} {o1 o2 : Occurrence Page}
    (h : state.pending = [o1, o2]) (hne : o1.request.page ≠ o2.request.page)
    (hlt : thresholdTime δ state o2.request.page < thresholdTime δ state o1.request.page) :
    nextPayment? (.threshold δ) state = some (thresholdTime δ state o2.request.page, o2.request.page) := by
  have hne' : (o2.request.page == o1.request.page) = false := by simp [Ne.symm hne]
  simp [nextPayment?, pendingPages, h, List.eraseDups, List.eraseDupsBy,
    List.eraseDupsBy.loop, hne', earlierPayment, hlt]

theorem nextAction_arrival {δ : Cost} {state : State Page} {occ : Occurrence Page}
    {rest : List (Occurrence Page)} (hu : state.unseen = occ :: rest)
    (hp : nextPayment? (.threshold δ) state = none) :
    nextAction? (.threshold δ) state = some (Action.arrival occ) := by
  simp [nextAction?, hu, hp]

theorem nextAction_arrival_of_le {δ : Cost} {state : State Page} {occ : Occurrence Page}
    {rest : List (Occurrence Page)} {t : Time} {p : Page} (hu : state.unseen = occ :: rest)
    (hp : nextPayment? (.threshold δ) state = some (t, p)) (hle : occ.request.arrival ≤ t) :
    nextAction? (.threshold δ) state = some (Action.arrival occ) := by
  simp [nextAction?, hu, hp, hle]

theorem nextAction_payment {δ : Cost} {state : State Page} {t : Time} {p : Page}
    (hp : nextPayment? (.threshold δ) state = some (t, p))
    (hu : ∀ occ rest, state.unseen = occ :: rest → t < occ.request.arrival) :
    nextAction? (.threshold δ) state = some (Action.payment t p) := by
  cases hs : state.unseen with
  | nil => simp [nextAction?, hs, hp]
  | cons occ rest =>
      have := hu occ rest hs
      simp [nextAction?, hs, hp, not_le.mpr this]

/-! ## Composing runs -/

theorem run_zero (δ : Cost) (input : Instance Page) (state : State Page) :
    run (.threshold δ) input 0 state = state := rfl

theorem run_step {δ : Cost} (input : Instance Page) (fuel : ℕ) {state : State Page}
    {action : Action Page} (h : nextAction? (.threshold δ) state = some action) :
    run (.threshold δ) input (fuel + 1) state = run (.threshold δ) input fuel (step input state action) := by
  rw [run, h]

theorem run_none {δ : Cost} (input : Instance Page) {state : State Page}
    (h : nextAction? (.threshold δ) state = none) : ∀ fuel, run (.threshold δ) input fuel state = state := by
  intro fuel
  induction fuel with
  | zero => rfl
  | succ fuel _ => rw [run, h]

theorem run_add {δ : Cost} (input : Instance Page) : ∀ (a b : ℕ) (state : State Page),
    run (.threshold δ) input (a + b) state = run (.threshold δ) input b (run (.threshold δ) input a state) := by
  intro a
  induction a with
  | zero => intro b state; rw [Nat.zero_add]; rfl
  | succ a ih =>
      intro b state
      cases h : nextAction? (.threshold δ) state with
      | none =>
          rw [run_none input h (a + 1 + b), run_none input h (a + 1), run_none input h b]
      | some act =>
          have e1 : run (.threshold δ) input (a + 1 + b) state = run (.threshold δ) input (a + b) (step input state act) := by
            rw [show a + 1 + b = (a + b) + 1 by omega]
            exact run_step input (a + b) h
          rw [e1, run_step input a h, ih b]

end
end PagingWithDelay.LowerBound
