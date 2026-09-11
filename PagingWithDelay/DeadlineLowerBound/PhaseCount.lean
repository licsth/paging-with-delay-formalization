import Mathlib.Data.Finset.Card
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The subset-and-mark counting engine of the `k + 1/2` deadline drafts

This file machine-checks the combinatorial core shared by
`combinatorial-lower-bound.tex` and `nonlazy-lower-bound.tex`: the adversary's
offline certificate `(c, L, q, m)`, its two operations, and the resulting bound

```text
(2k+1) * m_T ≤ 2T + 2k
```

after `T` operations, together with the arithmetic endgame that turns that
bound, plus `ALG ≥ T` and `OPT ≤ m_T + 1`, into "no competitive ratio below
`k + 1/2`".

Everything here lives in the `PhaseCount` namespace: `Certificate.lean` carries
the schedules of the same `(c, L, q, m)` data, and `Loop.lean` maintains the two
side by side.

It is deliberately *only* the counting engine.  Nothing here mentions
schedules, requests, delay, or an online algorithm, so nothing here checks the
two statements that connect the engine to the paging model:

* the drafts' certificate lemma — that the three schedule assertions really are
  maintained by the two operations (the offline side); and
* the drafts' charging lemma — that every operation can be charged to a
  distinct unit of online cost (the online side).

Those are what would have to be proved against `PagingWithDelay.Model` to get a
theorem about `Algorithm`.  What *is* established here is that the bookkeeping
producing the extra `1/2` is sound: a payment out of a marked singleton refills
`L` to `k` members and clears the mark, a payment out of an unmarked singleton
refills it to `k+1` members and marks one, processing steps remove at most one
member and never create a mark — and no sequence of operations does better than
`(2T+2k)/(2k+1)` payments.
-/

namespace PagingWithDelay.DeadlineLowerBound.PhaseCount

open Finset

variable {V : Type*} [DecidableEq V] {pages : Finset V} {k : ℕ}

/-- The adversary's offline certificate: the distinguished node `c` carrying the
unprocessed request, the set `L` of cheap candidate configurations, the mark
`q ∈ L ∪ {⊥}` naming the one cheap candidate that need not have a flagged
counterpart, and the budget `m`. -/
structure Certificate (V : Type*) [DecidableEq V] where
  distinguished : V
  cheap : Finset V
  mark : Option V
  budget : ℕ

namespace Certificate

/-- The drafts' `y = 2|L| - 1 + 1{q = ⊥}`, shifted by one to avoid truncated
subtraction on `ℕ`. -/
def potential (s : Certificate V) : ℕ :=
  2 * s.cheap.card + (if s.mark = none then 1 else 0)

/-- The certificate invariant: `L` is a nonempty subset of `V \ {c}`, the mark is
a member of `L` when present, and the potential has not exceeded its ceiling.
The ceiling encodes both `|L| ≤ k+1` and the fact that a `(k+1)`-element `L` is
only ever created together with a mark. -/
structure Valid (pages : Finset V) (k : ℕ) (s : Certificate V) : Prop where
  distinguished_mem : s.distinguished ∈ pages
  cheap_subset : s.cheap ⊆ pages.erase s.distinguished
  nonempty : s.cheap.Nonempty
  mark_mem : ∀ q ∈ s.mark, q ∈ s.cheap
  potential_le : s.potential ≤ 2 * k + 2

theorem Valid.distinguished_notMem {pages : Finset V} {k : ℕ} {s : Certificate V}
    (hs : s.Valid pages k) : s.distinguished ∉ s.cheap :=
  fun hmem => (Finset.mem_erase.mp (hs.cheap_subset hmem)).1 rfl

theorem Valid.mem_pages {pages : Finset V} {k : ℕ} {s : Certificate V}
    (hs : s.Valid pages k) {x : V} (hx : x ∈ s.cheap) : x ∈ pages :=
  Finset.mem_of_mem_erase (hs.cheap_subset hx)

end Certificate

/-- `K = pages \ {c, d}`: the `k` nodes that are neither the old distinguished
node nor the last cheap candidate.  This is the set `Certificate.lean` refills
the cheap family from, written the same way. -/
def refill (pages : Finset V) (c d : V) : Finset V := pages \ {c, d}

/-- One certificate operation.

`process` is the drafts' operation (F): a request at a node `x ≠ c` is
processed, `x` leaves the cheap set, and the mark is cleared if it was `x`.
The budget does not move.

`payShort` and `payLong` are the two branches of operation (P), available only
when the cheap set is a singleton `{d}`: `d` becomes the new distinguished node
and the cheap set is refilled with `V \ {c, d}`, together with the old
distinguished node `c` exactly when the mark was absent.  By
`pay_cases` these two branches exhaust the possibilities in a valid state, so
restricting to them costs the adversary nothing. -/
inductive Step (pages : Finset V) : Certificate V → Certificate V → Prop
  | process (s : Certificate V) (x : V) (hx : x ≠ s.distinguished)
      (hne : (s.cheap.erase x).Nonempty) :
      Step pages s
        { distinguished := s.distinguished
          cheap := s.cheap.erase x
          mark := if s.mark = some x then none else s.mark
          budget := s.budget }
  | payShort (s : Certificate V) (d : V) (hd : s.cheap = {d}) (hmark : s.mark = some d) :
      Step pages s
        { distinguished := d
          cheap := refill pages s.distinguished d
          mark := none
          budget := s.budget + 1 }
  | payLong (s : Certificate V) (d : V) (hd : s.cheap = {d}) (hmark : s.mark = none) :
      Step pages s
        { distinguished := d
          cheap := insert s.distinguished (refill pages s.distinguished d)
          mark := some s.distinguished
          budget := s.budget + 1 }

/-- In a valid state whose cheap set is the singleton `{d}`, the mark is either
`d` or absent: the two payment branches are exhaustive. -/
theorem pay_cases {s : Certificate V} {d : V} (hs : s.Valid pages k) (hd : s.cheap = {d}) :
    s.mark = some d ∨ s.mark = none := by
  cases hmark : s.mark with
  | none => exact Or.inr rfl
  | some q =>
      left
      have hq : q ∈ s.cheap := hs.mark_mem q (by rw [hmark]; rfl)
      rw [hd, Finset.mem_singleton] at hq
      rw [hq]

/-- `T` operations. -/
inductive Run (pages : Finset V) : Certificate V → ℕ → Certificate V → Prop
  | refl (s : Certificate V) : Run pages s 0 s
  | tail {s t u : Certificate V} {n : ℕ} :
      Run pages s n t → Step pages t u → Run pages s (n + 1) u

/-! ## The refill set -/

theorem card_refill (hcard : pages.card = k + 2) {c d : V} (hc : c ∈ pages) (hd : d ∈ pages)
    (hcd : c ≠ d) : (refill pages c d).card = k := by
  have hpair : ({c, d} : Finset V) ⊆ pages := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hc
    · rw [Finset.mem_singleton.mp hx]; exact hd
  have hcard_pair : ({c, d} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hcd), Finset.card_singleton]
  rw [refill, Finset.card_sdiff, Finset.inter_eq_left.mpr hpair, hcard_pair, hcard]
  omega

theorem notMem_refill_left (pages : Finset V) (c d : V) : c ∉ refill pages c d := by
  simp [refill]

theorem notMem_refill_right (pages : Finset V) (c d : V) : d ∉ refill pages c d := by
  simp [refill]

theorem refill_subset (pages : Finset V) (c d : V) : refill pages c d ⊆ pages := by
  intro x hx
  exact (Finset.mem_sdiff.mp hx).1

theorem refill_nonempty (hcard : pages.card = k + 2) (hk : 1 ≤ k) {c d : V}
    (hc : c ∈ pages) (hd : d ∈ pages) (hcd : c ≠ d) : (refill pages c d).Nonempty := by
  rw [← Finset.card_pos, card_refill hcard hc hd hcd]
  omega

/-! ## Why two short phases cannot be consecutive

This is the drafts' phase argument, and the source of the extra `1/2`.  A short
payment can only be taken from a marked state and leaves an unmarked one; no
processing step creates a mark; hence the payment ending the phase that follows
a short payment is long, refilling `L` to `k+1` members and so buying a phase of
`k+1` operations rather than `k`.  The potential argument below uses this
implicitly, through the `1{q = ⊥}` summand. -/

theorem Step.budget_mono {s t : Certificate V} (hstep : Step pages s t) : s.budget ≤ t.budget := by
  cases hstep <;> simp

theorem Run.budget_mono {s t : Certificate V} {T : ℕ} (hrun : Run pages s T t) :
    s.budget ≤ t.budget := by
  induction hrun with
  | refl => exact le_refl _
  | tail _ hstep ih => exact ih.trans hstep.budget_mono

/-- A short payment — a step that raises the budget and lands unmarked — can
only be taken from a marked state. -/
theorem Step.payShort_source_marked {s t : Certificate V} (hstep : Step pages s t)
    (hbudget : t.budget = s.budget + 1) (hunmarked : t.mark = none) : s.mark ≠ none := by
  cases hstep with
  | process x hx hne => simp at hbudget
  | payShort d hd hmark => simp [hmark]
  | payLong d hd hmark => simp at hunmarked

/-- A processing step — a step that leaves the budget alone — never creates a
mark. -/
theorem Step.mark_none_of_budget_eq {s t : Certificate V} (hstep : Step pages s t)
    (hbudget : t.budget = s.budget) (hs : s.mark = none) : t.mark = none := by
  cases hstep with
  | process x hx hne => simp [hs]
  | payShort d hd hmark => simp [hmark] at hs
  | payLong d hd hmark => simp at hbudget

/-- Between two payments the mark cannot reappear. -/
theorem Run.mark_none_of_budget_eq {s t : Certificate V} {T : ℕ} (hrun : Run pages s T t)
    (hbudget : t.budget = s.budget) (hs : s.mark = none) : t.mark = none := by
  induction hrun with
  | refl => exact hs
  | @tail middle u n hrun hstep ih =>
      have hmono₁ : s.budget ≤ middle.budget := hrun.budget_mono
      have hmono₂ : middle.budget ≤ u.budget := hstep.budget_mono
      have hmid : middle.budget = s.budget := by omega
      exact hstep.mark_none_of_budget_eq (by omega) (ih hmid)

/-- **Two short payments cannot be consecutive.**  If `s` is the state just after
a short payment, and only processing steps have happened since (the budget has
not moved), then the payment that ends the current phase is long: it leaves a
mark, and by `Step.payShort_source_marked` a short payment could not have been
taken. -/
theorem payment_after_short_is_long {s t u : Certificate V} {T : ℕ}
    (hshort : s.mark = none) (hrun : Run pages s T t) (hbudget : t.budget = s.budget)
    (hstep : Step pages t u) (hpay : u.budget = t.budget + 1) : u.mark ≠ none := by
  intro hunmarked
  exact hstep.payShort_source_marked hpay hunmarked (hrun.mark_none_of_budget_eq hbudget hshort)

/-! ## The invariant and the potential inequality -/

theorem Step.valid (hcard : pages.card = k + 2) (hk : 1 ≤ k)
    {s t : Certificate V} (hs : s.Valid pages k) (hstep : Step pages s t) : t.Valid pages k := by
  cases hstep with
  | process x hx hne =>
      refine ⟨hs.distinguished_mem,
        fun other hother => hs.cheap_subset (Finset.mem_of_mem_erase hother), hne, ?_, ?_⟩
      · intro q hq
        by_cases hmark : s.mark = some x
        · simp [hmark] at hq
        · simp only [hmark, if_false] at hq
          refine Finset.mem_erase.mpr ⟨fun hqx => hmark (hqx ▸ hq), hs.mark_mem q hq⟩
      · refine le_trans ?_ hs.potential_le
        simp only [Certificate.potential]
        have hcard' : (s.cheap.erase x).card ≤ s.cheap.card := Finset.card_erase_le
        by_cases hmark : s.mark = some x
        · have hmem : x ∈ s.cheap := hs.mark_mem x (by rw [hmark]; rfl)
          have hdrop : (s.cheap.erase x).card + 1 = s.cheap.card := by
            rw [Finset.card_erase_of_mem hmem]
            have : 1 ≤ s.cheap.card := Finset.card_pos.mpr ⟨x, hmem⟩
            omega
          have hnone : (if s.mark = none then 1 else 0) = 0 := by simp [hmark]
          simp only [hmark, if_true]
          omega
        · simp only [hmark, if_false]
          omega
  | payShort d hd hmark =>
      have hcd : s.distinguished ≠ d := by
        intro heq
        exact hs.distinguished_notMem (by rw [hd, heq]; simp)
      have hdpages : d ∈ pages := hs.mem_pages (by rw [hd]; simp)
      refine ⟨hdpages, ?_, refill_nonempty hcard hk hs.distinguished_mem hdpages hcd, by simp, ?_⟩
      · intro other hother
        refine Finset.mem_erase.mpr ⟨?_, refill_subset pages s.distinguished d hother⟩
        intro heq
        rw [heq] at hother
        exact notMem_refill_right pages s.distinguished d hother
      · simp only [Certificate.potential,
          card_refill hcard hs.distinguished_mem hdpages hcd]
        simp
  | payLong d hd hmark =>
      have hcd : s.distinguished ≠ d := by
        intro heq
        exact hs.distinguished_notMem (by rw [hd, heq]; simp)
      have hdpages : d ∈ pages := hs.mem_pages (by rw [hd]; simp)
      refine ⟨hdpages, ?_, ⟨s.distinguished, Finset.mem_insert_self _ _⟩, ?_, ?_⟩
      · intro other hother
        rcases Finset.mem_insert.mp hother with rfl | hother
        · exact Finset.mem_erase.mpr ⟨hcd, hs.distinguished_mem⟩
        · refine Finset.mem_erase.mpr ⟨?_, refill_subset pages s.distinguished d hother⟩
          intro heq
          rw [heq] at hother
          exact notMem_refill_right pages s.distinguished d hother
      · intro q hq
        simp only [Option.mem_def, Option.some.injEq] at hq
        rw [← hq]
        exact Finset.mem_insert_self _ _
      · simp only [Certificate.potential,
          Finset.card_insert_of_notMem (notMem_refill_left pages s.distinguished d),
          card_refill hcard hs.distinguished_mem hdpages hcd,
          if_neg (Option.some_ne_none s.distinguished)]
        omega

/-- The per-step inequality behind the drafts' potential argument: a payment
buys `2k+1` units of potential, a processing step gives back at most two.  Both
payment branches meet it with equality, which is why the bound is tight. -/
theorem Step.potential_le (hcard : pages.card = k + 2)
    {s t : Certificate V} (hs : s.Valid pages k) (hstep : Step pages s t) :
    s.potential + (2 * k + 1) * t.budget ≤ t.potential + 2 + (2 * k + 1) * s.budget := by
  cases hstep with
  | process x hx hne =>
      simp only [Certificate.potential]
      have hcard' : s.cheap.card ≤ (s.cheap.erase x).card + 1 := by
        by_cases hmem : x ∈ s.cheap
        · rw [Finset.card_erase_of_mem hmem]
          have : 1 ≤ s.cheap.card := Finset.card_pos.mpr ⟨x, hmem⟩
          omega
        · rw [Finset.erase_eq_of_notMem hmem]
          omega
      have hlink : (if s.mark = none then 1 else 0) ≤
          (if (if s.mark = some x then none else s.mark) = none then 1 else 0) := by
        by_cases hnone : s.mark = none
        · simp [hnone]
        · simp [hnone]
      omega
  | payShort d hd hmark =>
      have hcd : s.distinguished ≠ d := by
        intro heq
        exact hs.distinguished_notMem (by rw [hd, heq]; simp)
      have hdpages : d ∈ pages := hs.mem_pages (by rw [hd]; simp)
      have hcheap : s.cheap.card = 1 := by rw [hd]; simp
      have hnone : (if s.mark = none then 1 else 0) = 0 := by simp [hmark]
      have hexpand : (2 * k + 1) * (s.budget + 1) = (2 * k + 1) * s.budget + (2 * k + 1) := by
        ring
      simp only [Certificate.potential, hcheap, hnone,
        card_refill hcard hs.distinguished_mem hdpages hcd, hexpand]
      norm_num
      omega
  | payLong d hd hmark =>
      have hcd : s.distinguished ≠ d := by
        intro heq
        exact hs.distinguished_notMem (by rw [hd, heq]; simp)
      have hdpages : d ∈ pages := hs.mem_pages (by rw [hd]; simp)
      have hcheap : s.cheap.card = 1 := by rw [hd]; simp
      have hexpand : (2 * k + 1) * (s.budget + 1) = (2 * k + 1) * s.budget + (2 * k + 1) := by
        ring
      simp only [Certificate.potential, hcheap, hmark,
        Finset.card_insert_of_notMem (notMem_refill_left pages s.distinguished d),
        card_refill hcard hs.distinguished_mem hdpages hcd, hexpand,
        if_neg (Option.some_ne_none s.distinguished)]
      norm_num
      omega

/-! ## The bound after `T` operations -/

theorem Run.valid (hcard : pages.card = k + 2) (hk : 1 ≤ k)
    {s t : Certificate V} {T : ℕ} (hs : s.Valid pages k) (hrun : Run pages s T t) : t.Valid pages k := by
  induction hrun with
  | refl => exact hs
  | tail _ hstep ih => exact Step.valid hcard hk ih hstep

theorem Run.potential_le (hcard : pages.card = k + 2) (hk : 1 ≤ k)
    {s t : Certificate V} {T : ℕ} (hs : s.Valid pages k) (hrun : Run pages s T t) :
    s.potential + (2 * k + 1) * t.budget ≤
      t.potential + 2 * T + (2 * k + 1) * s.budget := by
  induction hrun with
  | refl => simp
  | @tail middle u n hrun hstep ih =>
      have hmiddle : middle.Valid pages k := Run.valid hcard hk hs hrun
      have hstep' := Step.potential_le hcard hmiddle hstep
      linarith

/-- **The counting bound of both drafts.**  A run of `T` certificate operations
from the initial state makes at most `(2T + 2k)/(2k+1)` payments. -/
theorem budget_bound (hcard : pages.card = k + 2) (hk : 1 ≤ k)
    {s t : Certificate V} {T : ℕ} (hs : s.Valid pages k) (hstart : s.potential = 2)
    (hbudget : s.budget = 0) (hrun : Run pages s T t) :
    (2 * k + 1) * t.budget ≤ 2 * T + 2 * k := by
  have hle := Run.potential_le hcard hk hs hrun
  have hceiling := (Run.valid hcard hk hs hrun).potential_le
  rw [hstart, hbudget] at hle
  omega

/-! ## The initial certificate -/

/-- The drafts' initial certificate: cheap set `{d}`, marked, budget zero. -/
def initial (c d : V) : Certificate V :=
  { distinguished := c, cheap := {d}, mark := some d, budget := 0 }

theorem initial_valid (hk : 1 ≤ k) {c d : V} (hc : c ∈ pages) (hd : d ∈ pages) (hcd : c ≠ d) :
    (initial c d).Valid pages k where
  distinguished_mem := hc
  cheap_subset := by
    intro x hx
    simp only [initial, Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_erase.mpr ⟨fun heq => hcd heq.symm, hd⟩
  nonempty := ⟨d, by simp [initial]⟩
  mark_mem := by
    intro q hq
    simp only [initial, Option.mem_def, Option.some.injEq] at hq
    simp [initial, hq]
  potential_le := by
    have h : (initial c d).potential = 2 := by simp [initial, Certificate.potential]
    omega

theorem initial_potential {c d : V} : (initial c d).potential = 2 := by
  simp [initial, Certificate.potential]

theorem initial_budget {c d : V} : (initial c d).budget = 0 := rfl

/-- **The counting bound from the initial certificate.** -/
theorem budget_bound_initial (hcard : pages.card = k + 2) (hk : 1 ≤ k)
    {c d : V} (hc : c ∈ pages) (hd : d ∈ pages) (hcd : c ≠ d) {t : Certificate V} {T : ℕ}
    (hrun : Run pages (initial c d) T t) :
    (2 * k + 1) * t.budget ≤ 2 * T + 2 * k :=
  budget_bound hcard hk (initial_valid hk hc hd hcd) initial_potential initial_budget hrun

/-! ## The arithmetic endgame

`ALG ≥ T` and `OPT ≤ m_T + 1` together with the counting bound leave no
competitive ratio below `k + 1/2`, whatever additive constant is granted.  The
hypothesis `2 * r < 2 * k + 1` is `r < k + 1/2` written without division. -/

theorem no_ratio_below_k_add_half (k : ℕ) (r β slack : NNReal)
    (hr : 2 * r < 2 * (k : NNReal) + 1) :
    ∃ T : ℕ, ∀ m alg opt : NNReal,
      (T : NNReal) ≤ alg → (2 * (k : NNReal) + 1) * m ≤ 2 * T + 2 * k → opt ≤ m + slack →
        r * opt + β < alg := by
  have hrreal : 2 * (r : ℝ) < 2 * (k : ℝ) + 1 := by exact_mod_cast hr
  have hpos : (0 : ℝ) < 2 * (k : ℝ) + 1 - 2 * r := by linarith
  obtain ⟨T, hT⟩ :=
    exists_nat_gt (((4 * (k : ℝ) + 1) * r + (2 * (k : ℝ) + 1) * (r * slack + β)) /
      (2 * (k : ℝ) + 1 - 2 * r))
  refine ⟨T, fun m alg opt halg hm hopt => ?_⟩
  rw [div_lt_iff₀ hpos] at hT
  have hmreal : (2 * (k : ℝ) + 1) * m ≤ 2 * T + 2 * k := by exact_mod_cast hm
  have hoptreal : (opt : ℝ) ≤ m + slack := by exact_mod_cast hopt
  have halgreal : (T : ℝ) ≤ alg := by exact_mod_cast halg
  have hrnn : (0 : ℝ) ≤ r := r.coe_nonneg
  have hkey : (r : ℝ) * opt + β < T := by
    nlinarith [mul_le_mul_of_nonneg_left hmreal hrnn,
      mul_le_mul_of_nonneg_left hoptreal hrnn]
  have : (r : ℝ) * opt + β < alg := lt_of_lt_of_le hkey halgreal
  exact_mod_cast this

/-! ## The engine is not vacuous, and the bound is tight

With `k = 2` the adversary can be driven through a short payment, one
processing step and a long payment: three operations, two payments, and
`(2k+1) * 2 = 10 = 2 * 3 + 2 * 2`.  So the operations really are available, and
`budget_bound` is met with equality — the drafts' phase count cannot be
improved without changing the certificate. -/

example : ∃ t : Certificate (Fin 4),
    Run Finset.univ (initial (0 : Fin 4) 1) 3 t ∧ t.budget = 2 :=
  ⟨_, Run.tail (Run.tail (Run.tail (Run.refl _)
        (Step.payShort _ 1 rfl rfl))
        (Step.process _ 2 (by decide) (by decide)))
        (Step.payLong _ 3 (by decide) (by decide)), rfl⟩

example : (2 * 2 + 1) * 2 = 2 * 3 + 2 * 2 := by norm_num

end PagingWithDelay.DeadlineLowerBound.PhaseCount
