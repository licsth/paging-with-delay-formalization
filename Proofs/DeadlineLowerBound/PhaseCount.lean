import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

/-!
# The subset-and-mark counting engine of the `k + 1/2` deadline drafts

This file checks the combinatorial core of the write-up's Lemma
`lem:deadlines_opt_upper_bound` (Section 5 of `submission.tex`): the adversary's
offline certificate `(c, L, q, m)`, its two operations, and the bound

```text
(2k+1) * m_T ≤ 2T + 2k
```

after `T` operations.  Nothing here mentions schedules, requests or an online
algorithm: `Certificate.lean` proves that the schedule invariants `lb_inv_1`–`lb_inv_3`
are maintained by the same operations, `Charging.lean` and `Online.lean` charge
every operation to the online algorithm, and `Loop.lean` runs everything side by side.

The bookkeeping producing the extra `1/2`: a payment out of a marked singleton
refills `L` to `k` members and clears the mark, a payment out of an unmarked
singleton refills it to `k+1` members and marks one, and processing steps
remove at most one member and never create a mark.
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

theorem Valid.mem_pages {pages : Finset V} {k : ℕ} {s : Certificate V}
    (hs : s.Valid pages k) {x : V} (hx : x ∈ s.cheap) : x ∈ pages :=
  Finset.mem_of_mem_erase (hs.cheap_subset hx)

/-- In a payment, the last cheap candidate `d` is a page other than `c`. -/
theorem Valid.pay_facts {s : Certificate V} (hs : s.Valid pages k) {d : V}
    (hd : s.cheap = {d}) : d ∈ pages ∧ s.distinguished ≠ d := by
  have h := hs.cheap_subset (hd ▸ Finset.mem_singleton_self d)
  exact ⟨Finset.mem_of_mem_erase h, (Finset.ne_of_mem_erase h).symm⟩

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
  | some q => simpa [hd] using hs.mark_mem q hmark

/-- `T` operations. -/
inductive Run (pages : Finset V) : Certificate V → ℕ → Certificate V → Prop
  | refl (s : Certificate V) : Run pages s 0 s
  | tail {s t u : Certificate V} {n : ℕ} :
      Run pages s n t → Step pages t u → Run pages s (n + 1) u

/-! ## The refill set -/

theorem card_refill (hcard : pages.card = k + 2) {c d : V} (hc : c ∈ pages) (hd : d ∈ pages)
    (hcd : c ≠ d) : (refill pages c d).card = k := by
  rw [refill, Finset.card_sdiff_of_subset (Finset.insert_subset hc (by simpa using hd)),
    Finset.card_pair hcd, hcard]
  rfl

theorem notMem_refill_left (pages : Finset V) (c d : V) : c ∉ refill pages c d := by
  simp [refill]

theorem refill_nonempty (hcard : pages.card = k + 2) (hk : 1 ≤ k) {c d : V}
    (hc : c ∈ pages) (hd : d ∈ pages) (hcd : c ≠ d) : (refill pages c d).Nonempty := by
  rw [← Finset.card_pos, card_refill hcard hc hd hcd]
  omega

/-! ## The invariant and the potential inequality

The potential's summand `1{q = ⊥}` encodes the drafts' phase argument: a short
payment can only be taken from a marked state and leaves an unmarked one, and no
processing step creates a mark, so the payment after a short one is long. -/

theorem Step.valid (hcard : pages.card = k + 2) (hk : 1 ≤ k)
    {s t : Certificate V} (hs : s.Valid pages k) (hstep : Step pages s t) : t.Valid pages k := by
  cases hstep with
  | process x hx hne =>
      refine ⟨hs.distinguished_mem, (Finset.erase_subset _ _).trans hs.cheap_subset, hne, ?_,
        le_trans ?_ hs.potential_le⟩
      · intro q hq
        split_ifs at hq with hmark
        · simp at hq
        · exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hmark hq, hs.mark_mem q hq⟩
      · simp only [Certificate.potential]
        by_cases hmark : s.mark = some x
        · have := Finset.card_erase_add_one (hs.mark_mem x hmark)
          simp only [hmark, if_true, reduceCtorEq, if_false]
          omega
        · have := Finset.card_erase_le (s := s.cheap) (a := x)
          simp only [hmark, if_false]
          omega
  | payShort d hd hmark =>
      obtain ⟨hdp, hcd⟩ := hs.pay_facts hd
      refine ⟨hdp, fun y hy => ?_, refill_nonempty hcard hk hs.distinguished_mem hdp hcd, by simp,
        by simp [Certificate.potential, card_refill hcard hs.distinguished_mem hdp hcd]⟩
      simp only [refill, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hy
      exact Finset.mem_erase.mpr ⟨fun h => hy.2 (Or.inr h), hy.1⟩
  | payLong d hd hmark =>
      obtain ⟨hdp, hcd⟩ := hs.pay_facts hd
      refine ⟨hdp, fun y hy => ?_, Finset.insert_nonempty _ _, by simp, ?_⟩
      · simp only [refill, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at hy
        rcases hy with rfl | hy
        · exact Finset.mem_erase.mpr ⟨hcd, hs.distinguished_mem⟩
        · exact Finset.mem_erase.mpr ⟨fun h => hy.2 (Or.inr h), hy.1⟩
      · simp [Certificate.potential, Finset.card_insert_of_notMem (notMem_refill_left _ _ _),
          card_refill hcard hs.distinguished_mem hdp hcd]
        omega

/-- The per-step inequality behind the drafts' potential argument: a payment
buys `2k+1` units of potential, a processing step gives back at most two.  Both
payment branches meet it with equality, which is why the bound is tight. -/
theorem Step.potential_le (hcard : pages.card = k + 2)
    {s t : Certificate V} (hs : s.Valid pages k) (hstep : Step pages s t) :
    s.potential + (2 * k + 1) * t.budget ≤ t.potential + 2 + (2 * k + 1) * s.budget := by
  cases hstep with
  | process x hx hne =>
      have := Finset.pred_card_le_card_erase (s := s.cheap) (a := x)
      simp only [Certificate.potential]
      split_ifs <;> simp_all <;> omega
  | payShort d hd hmark =>
      obtain ⟨hdp, hcd⟩ := hs.pay_facts hd
      simp [Certificate.potential, hd, hmark, card_refill hcard hs.distinguished_mem hdp hcd]
      ring_nf
      omega
  | payLong d hd hmark =>
      obtain ⟨hdp, hcd⟩ := hs.pay_facts hd
      simp [Certificate.potential, hd, hmark,
        Finset.card_insert_of_notMem (notMem_refill_left _ _ _), card_refill hcard hs.distinguished_mem hdp hcd]
      ring_nf
      omega

/-! ## The bound after `T` operations -/

theorem Run.valid (hcard : pages.card = k + 2) (hk : 1 ≤ k)
    {s t : Certificate V} {T : ℕ} (hs : s.Valid pages k) (hrun : Run pages s T t) :
    t.Valid pages k := by
  induction hrun with
  | refl => exact hs
  | tail _ hstep ih => exact Step.valid hcard hk ih hstep

theorem Run.potential_le (hcard : pages.card = k + 2) (hk : 1 ≤ k)
    {s t : Certificate V} {T : ℕ} (hs : s.Valid pages k) (hrun : Run pages s T t) :
    s.potential + (2 * k + 1) * t.budget ≤
      t.potential + 2 * T + (2 * k + 1) * s.budget := by
  induction hrun with
  | refl => simp
  | tail hrun hstep ih =>
      have := Step.potential_le hcard (Run.valid hcard hk hs hrun) hstep
      omega

/-! ## The initial certificate -/

/-- The drafts' initial certificate: cheap set `{d}`, marked, budget zero. -/
def initial (c d : V) : Certificate V :=
  { distinguished := c, cheap := {d}, mark := some d, budget := 0 }

theorem initial_valid {c d : V} (hc : c ∈ pages) (hd : d ∈ pages) (hcd : c ≠ d) :
    (initial c d).Valid pages k where
  distinguished_mem := hc
  cheap_subset := by simp [initial, Finset.mem_erase, hd, Ne.symm hcd]
  nonempty := Finset.singleton_nonempty d
  mark_mem := by simp [initial]
  potential_le := by simp [initial, Certificate.potential]

/-- **The counting bound of both drafts.**  A run of `T` certificate operations
from the initial certificate makes at most `(2T + 2k)/(2k+1)` payments. -/
theorem budget_bound (hcard : pages.card = k + 2) (hk : 1 ≤ k)
    {c d : V} (hc : c ∈ pages) (hd : d ∈ pages) (hcd : c ≠ d) {t : Certificate V} {T : ℕ}
    (hrun : Run pages (initial c d) T t) :
    (2 * k + 1) * t.budget ≤ 2 * T + 2 * k := by
  have hs := initial_valid (k := k) hc hd hcd
  have hle := Run.potential_le hcard hk hs hrun
  have hceiling := (Run.valid hcard hk hs hrun).potential_le
  rw [show (initial c d).potential = 2 by simp [initial, Certificate.potential],
    show (initial c d).budget = 0 from rfl] at hle
  omega

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
