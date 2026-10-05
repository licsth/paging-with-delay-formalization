import Proofs.DeadlineLowerBound.Offline

/-!
# The offline certificate of the deadline lower bound

The write-up's invariants `lb_inv_1`–`lb_inv_3` (Section 5 of `submission.tex`)
assert, in the notation below, that the data
`(c, L, q, m)` — a distinguished node, a set of cheap candidates, a mark and a
budget — carries three families of offline schedules, and that the two
operations (F) and (P) preserve them:

1. every configuration `C_z = V \ {c, z}`, `z ≠ c`, is reachable at cost `m+1`;
2. every `C_z` with `z ∈ L` is reachable at cost `m`;
3. every `C_z` with `z ∈ L \ {q}` is reachable at cost `m+1` by a schedule that
   has *already served* the distinguished request `α` at `c`.

`Certificate` below is that statement, and `Certificate.process`,
`Certificate.pay_short` and `Certificate.pay_long` are the three transitions,
proved.  They mirror `Step.process`, `Step.payShort` and `Step.payLong` of
`PhaseCount.lean`, which counts them.

Two remarks on the translation.

* Service here is `Model.lean`'s: a page in the cache when the request arrives
  serves it at zero delay.  The certificate therefore never needs a request's
  deadline except for the distinguished request `α`, whose window must still be
  open at the checkpoint — the draft's requirement `u < D` on auxiliary requests
  is bookkeeping for the online side, not something the offline side needs.
* The cardinality of `V` plays no part; what the payment operation actually
  needs is that `V \ {c, d}` is nonempty, which is where `k ≥ 1` enters.
-/

namespace PagingWithDelay.DeadlineLowerBound

open Finset

noncomputable section

variable {Page : Type*} [DecidableEq Page]

theorem mem_diff_pair {V : Finset Page} {p f y : Page} :
    y ∈ V \ {p, f} ↔ y ∈ V ∧ y ≠ p ∧ y ≠ f := by
  simp [Finset.mem_sdiff, not_or]

/-- From the configuration missing `p` and `f`, fetching `f` and evicting `e`
gives the configuration missing `p` and `e`.  Every move the certificate makes
is of this shape. -/
theorem applyMove_pair {V : Finset Page} {p f e : Page} (hf : f ∈ V) (hfp : f ≠ p) (hfe : f ≠ e)
    (t : Time) : applyMove (V \ {p, f}) ⟨t, f, e⟩ = V \ {p, e} := by
  ext y
  simp only [applyMove, Finset.mem_insert, Finset.mem_erase, mem_diff_pair]
  constructor
  · rintro (rfl | ⟨hye, hy, hyp, _⟩)
    · exact ⟨hf, hfp, hfe⟩
    · exact ⟨hy, hyp, hye⟩
  · rintro ⟨hy, hyp, hye⟩
    by_cases hyf : y = f
    · exact Or.inl hyf
    · exact Or.inr ⟨hye, hy, hyp, hyf⟩

/-- **The certificate.**  `processed` are the requests already charged to the
schedules, `alpha` the distinguished request pending at `c`, and `now` the
checkpoint. -/
structure Certificate (V start : Finset Page) (processed : List (Window Page))
    (alpha : Window Page) (c : Page) (L : Finset Page) (q : Option Page) (m : ℕ)
    (now : Time) : Prop where
  distinguished_mem : c ∈ V
  cheap_subset : L ⊆ V.erase c
  cheap_nonempty : L.Nonempty
  mark_mem : ∀ x ∈ q, x ∈ L
  alpha_page : alpha.page = c
  alpha_arrival : alpha.arrival ≤ now
  alpha_open : now < alpha.deadline
  processed_before : ∀ w ∈ processed, w.arrival ≤ now
  background : ∀ z ∈ V.erase c, Reaches start processed now (m + 1) (V \ {c, z})
  cheap : ∀ z ∈ L, Reaches start processed now m (V \ {c, z})
  flagged : ∀ z ∈ L, q ≠ some z →
    Reaches start (alpha :: processed) now (m + 1) (V \ {c, z})

namespace Certificate

variable {V start : Finset Page} {processed : List (Window Page)} {alpha : Window Page}
  {c : Page} {L : Finset Page} {q : Option Page} {m : ℕ} {now : Time}

theorem cheap_mem_V (hcert : Certificate V start processed alpha c L q m now) {z : Page}
    (hz : z ∈ L) : z ∈ V ∧ z ≠ c := by
  have := hcert.cheap_subset hz
  exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩

/-! ## Operation (F): processing a request away from `c` -/

/-- **Operation (F).**  A request `gamma` at a node `x ≠ c` that arrives after
the checkpoint is processed: `x` leaves the cheap set, the mark goes with it if
it was `x`, and the budget does not move.  The new checkpoint `u` may be any
time at or after `gamma`'s arrival at which `alpha`'s window is still open. -/
theorem process (hcert : Certificate V start processed alpha c L q m now)
    {x : Page} (hx : x ∈ V.erase c) (hnonempty : (L.erase x).Nonempty)
    {gamma : Window Page} (hpage : gamma.page = x) (harrival : now < gamma.arrival)
    {u : Time} (hu : gamma.arrival ≤ u) (hopen : u < alpha.deadline) :
    Certificate V start (gamma :: processed) alpha c (L.erase x)
      (if q = some x then none else q) m u := by
  obtain ⟨a, ha⟩ := hnonempty
  have hax : a ≠ x := Finset.ne_of_mem_erase ha
  have haL : a ∈ L := Finset.mem_of_mem_erase ha
  have hxV : x ∈ V := Finset.mem_of_mem_erase hx
  have hxc : x ≠ c := Finset.ne_of_mem_erase hx
  have hnow_u : now < u := lt_of_lt_of_le harrival hu
  have harrivals : ∀ w ∈ gamma :: processed, w.arrival ≤ u := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hu
    · exact (hcert.processed_before w hw).trans hnow_u.le
  -- a cheap schedule whose index is not `x` is sitting on `x`, so it serves
  -- `gamma` without moving
  have hcheap_serves : ∀ z ∈ L, z ≠ x →
      Reaches start (gamma :: processed) now m (V \ {c, z}) := by
    intro z hz hzx
    refine (hcert.cheap z hz).serves_of_mem gamma ?_ harrival
    rw [hpage]
    exact mem_diff_pair.mpr ⟨hxV, hxc, fun heq => hzx heq.symm⟩
  refine ⟨hcert.distinguished_mem, ?_, ⟨a, ha⟩, ?_, hcert.alpha_page,
    hcert.alpha_arrival.trans hnow_u.le, hopen, harrivals, ?_, ?_, ?_⟩
  · exact fun z hz => hcert.cheap_subset (Finset.mem_of_mem_erase hz)
  · intro y hy
    by_cases hq : q = some x
    · rw [hq] at hy; simp at hy
    · rw [if_neg hq] at hy
      have hyL : y ∈ L := hcert.mark_mem y hy
      refine Finset.mem_erase.mpr ⟨?_, hyL⟩
      intro hyx
      exact hq (by rw [← hyx]; exact Option.mem_def.mp hy)
  · -- background: rebuild every candidate from the cheap schedule at `a`
    intro z hz
    have hzV : z ∈ V := Finset.mem_of_mem_erase hz
    have hzc : z ≠ c := Finset.ne_of_mem_erase hz
    by_cases hza : z = a
    · rw [hza]
      exact ((hcheap_serves a haL hax).mono_now hnow_u.le).mono_cost (Nat.le_succ m)
    · have hbase := hcheap_serves a haL hax
      have hstep := hbase.step ⟨u, a, z⟩ hnow_u
        (mem_diff_pair.mpr ⟨hzV, hzc, hza⟩)
        (fun hmemA => (mem_diff_pair.mp hmemA).2.2 rfl)
        harrivals
      rwa [applyMove_pair (hcert.cheap_mem_V haL).1 (hcert.cheap_mem_V haL).2
        (fun heq => hza heq.symm) u] at hstep
  · -- cheap: the surviving candidates keep their schedules
    intro z hz
    exact (hcheap_serves z (Finset.mem_of_mem_erase hz)
      (Finset.ne_of_mem_erase hz)).mono_now hnow_u.le
  · -- flagged: likewise, and they keep their service of `alpha`
    intro z hz hq'
    have hzL : z ∈ L := Finset.mem_of_mem_erase hz
    have hzx : z ≠ x := Finset.ne_of_mem_erase hz
    have hqz : q ≠ some z := by
      by_cases hq : q = some x
      · rw [hq]
        intro heq
        exact hzx (Option.some.inj heq).symm
      · rw [if_neg hq] at hq'
        exact hq'
    have hserved : Reaches start (gamma :: alpha :: processed) now (m + 1) (V \ {c, z}) := by
      refine (hcert.flagged z hzL hqz).serves_of_mem gamma ?_ harrival
      rw [hpage]
      exact mem_diff_pair.mpr ⟨hxV, hxc, fun heq => hzx heq.symm⟩
    refine (hserved.mono_now hnow_u.le).subset ?_
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)

/-! ## Operation (P): paying, and promoting the reserve request

The payment is where the mark does its work.  Both branches refill the cheap
set from `V \ {c, d}`, and the long branch — available exactly when no cheap
candidate lacks a flagged counterpart — keeps the old flagged schedule at `d`
as one extra cheap candidate, at the price of leaving *it* unflagged.
-/

variable {d : Page} {beta : Window Page} {u : Time}

/-- The three schedule families the payment builds, shared by its two branches.
The first is the new cheap family, the second their flagged counterparts, and
the third the one background candidate whose index is the old distinguished
node — the draft's round trip. -/
private theorem pay_pieces (hcert : Certificate V start processed alpha c L q m now)
    (hL : L = {d}) (hK : (V \ {c, d}).Nonempty)
    (hpage : beta.page = d) (harrival : now < beta.arrival)
    (hbeta : beta.arrival < u) (halpha : u ≤ alpha.deadline) :
    (∀ z ∈ V \ {c, d}, Reaches start (alpha :: processed) u (m + 1) (V \ {d, z})) ∧
      (∀ z ∈ V \ {c, d},
        Reaches start (beta :: alpha :: processed) u (m + 2) (V \ {d, z})) ∧
      Reaches start (alpha :: processed) u (m + 2) (V \ {d, c}) := by
  have hdL : d ∈ L := by rw [hL]; simp
  have hdV : d ∈ V := (hcert.cheap_mem_V hdL).1
  have hdc : d ≠ c := (hcert.cheap_mem_V hdL).2
  have hcV : c ∈ V := hcert.distinguished_mem
  have hnow_u : now < u := harrival.trans hbeta
  have hpair : V \ ({c, d} : Finset Page) = V \ {d, c} := by rw [Finset.pair_comm]
  have hcnot : c ∉ V \ ({c, d} : Finset Page) := fun h => (mem_diff_pair.mp h).2.1 rfl
  have hprocessed : ∀ w ∈ processed, w.arrival ≤ u := fun w hw =>
    (hcert.processed_before w hw).trans hnow_u.le
  have halpha_page : c = alpha.page := hcert.alpha_page.symm
  have halpha_arr : alpha.arrival ≤ u := hcert.alpha_arrival.trans hnow_u.le
  -- the new cheap family: from the old cheap schedule at `d`, fetch `c`
  have hcheap : ∀ z ∈ V \ ({c, d} : Finset Page),
      Reaches start (alpha :: processed) u (m + 1) (V \ {d, z}) := by
    intro z hz
    obtain ⟨hzV, hzc, hzd⟩ := mem_diff_pair.mp hz
    have hstep := (hcert.cheap d hdL).step_serving ⟨u, c, z⟩ alpha hnow_u hz hcnot
      hprocessed halpha_page halpha_arr halpha
    rw [hpair, applyMove_pair hcV hdc.symm (fun heq => hzc heq.symm) u] at hstep
    exact hstep
  -- their flagged counterparts: from the background schedule at `z`, which is
  -- sitting on `d` when `beta` arrives, then fetch `c`
  have hflagged : ∀ z ∈ V \ ({c, d} : Finset Page),
      Reaches start (beta :: alpha :: processed) u (m + 2) (V \ {d, z}) := by
    intro z hz
    obtain ⟨hzV, hzc, hzd⟩ := mem_diff_pair.mp hz
    have hbackground := hcert.background z (Finset.mem_erase.mpr ⟨hzc, hzV⟩)
    have hsits : beta.page ∈ V \ ({c, z} : Finset Page) := by
      rw [hpage]
      exact mem_diff_pair.mpr ⟨hdV, hdc, fun heq => hzd heq.symm⟩
    have hserved := hbackground.serves_of_mem beta hsits harrival
    have hstep := hserved.step_serving ⟨u, c, d⟩ alpha hnow_u
      (mem_diff_pair.mpr ⟨hdV, hdc, fun heq => hzd heq.symm⟩)
      (fun h => (mem_diff_pair.mp h).2.1 rfl)
      (by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hbeta.le
        · exact hprocessed w hw)
      halpha_page halpha_arr halpha
    rw [show V \ ({c, z} : Finset Page) = V \ {z, c} by rw [Finset.pair_comm],
      applyMove_pair hcV (fun heq => hzc heq.symm) hdc.symm u,
      show V \ ({z, d} : Finset Page) = V \ {d, z} by rw [Finset.pair_comm]] at hstep
    refine hstep.subset ?_
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)
  -- the round trip, for the candidate indexed by the old distinguished node
  refine ⟨hcheap, hflagged, ?_⟩
  obtain ⟨w, hw⟩ := hK
  obtain ⟨hwV, hwc, hwd⟩ := mem_diff_pair.mp hw
  obtain ⟨t₁, hnow_t₁, ht₁_u⟩ := exists_between hnow_u
  have hout := (hcert.cheap d hdL).step_serving ⟨t₁, c, w⟩ alpha hnow_t₁ hw hcnot
    (fun v hv => (hcert.processed_before v hv).trans hnow_t₁.le)
    halpha_page (hcert.alpha_arrival.trans hnow_t₁.le) (ht₁_u.le.trans halpha)
  rw [hpair, applyMove_pair hcV hdc.symm (fun heq => hwc heq.symm) t₁] at hout
  have hback := hout.step ⟨u, w, c⟩ ht₁_u
    (mem_diff_pair.mpr ⟨hcV, hdc.symm, fun heq => hwc heq.symm⟩)
    (fun h => (mem_diff_pair.mp h).2.2 rfl)
    (by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact halpha_arr
      · exact hprocessed v hv)
  rwa [applyMove_pair hwV hwd hwc u] at hback

/-- **Operation (P), short payment.**  The mark sits on the last cheap
candidate, so the old flagged family is empty and the new cheap set is just
`V \ {c, d}` — `k` candidates, all of them flagged.

The mark hypothesis `_hq` is not used: the short payment is available whatever
the mark is.  It is kept so that the transitions here match
`PhaseCount.Step.payShort` one for one — the mark is what tells the adversary
that the *long* payment is available instead, and by `PhaseCount.pay_cases`
exactly one of the two branches applies in any state. -/
theorem pay_short (hcert : Certificate V start processed alpha c L q m now)
    (hL : L = {d}) (_hq : q = some d) (hK : (V \ {c, d}).Nonempty)
    (hpage : beta.page = d) (harrival : now < beta.arrival)
    (hbeta : beta.arrival < u) (halpha : u ≤ alpha.deadline) (hopen : u < beta.deadline) :
    Certificate V start (alpha :: processed) beta d (V \ {c, d}) none (m + 1) u := by
  obtain ⟨hcheap, hflagged, hround⟩ :=
    pay_pieces hcert hL hK hpage harrival hbeta halpha
  have hdL : d ∈ L := by rw [hL]; simp
  have hdV : d ∈ V := (hcert.cheap_mem_V hdL).1
  have hdc : d ≠ c := (hcert.cheap_mem_V hdL).2
  have hnow_u : now < u := harrival.trans hbeta
  refine ⟨hdV, ?_, hK, by simp, hpage, hbeta.le, hopen, ?_, ?_, hcheap, ?_⟩
  · intro z hz
    obtain ⟨hzV, _, hzd⟩ := mem_diff_pair.mp hz
    exact Finset.mem_erase.mpr ⟨hzd, hzV⟩
  · intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hcert.alpha_arrival.trans hnow_u.le
    · exact (hcert.processed_before w hw).trans hnow_u.le
  · intro z hz
    have hzV : z ∈ V := Finset.mem_of_mem_erase hz
    have hzd : z ≠ d := Finset.ne_of_mem_erase hz
    by_cases hzc : z = c
    · rw [hzc]; exact hround
    · exact (hcheap z (mem_diff_pair.mpr ⟨hzV, hzc, hzd⟩)).mono_cost (Nat.le_succ _)
  · intro z hz _
    exact hflagged z hz

/-- **Operation (P), long payment.**  No cheap candidate lacks a flagged
counterpart, so the old flagged schedule at `d` — which has already served
`alpha` — survives as a `(k+1)`-st cheap candidate, and becomes the new
unflagged one. -/
theorem pay_long (hcert : Certificate V start processed alpha c L q m now)
    (hL : L = {d}) (hq : q = none) (hK : (V \ {c, d}).Nonempty)
    (hpage : beta.page = d) (harrival : now < beta.arrival)
    (hbeta : beta.arrival < u) (halpha : u ≤ alpha.deadline) (hopen : u < beta.deadline) :
    Certificate V start (alpha :: processed) beta d
      (insert c (V \ {c, d})) (some c) (m + 1) u := by
  obtain ⟨hcheap, hflagged, hround⟩ :=
    pay_pieces hcert hL hK hpage harrival hbeta halpha
  have hdL : d ∈ L := by rw [hL]; simp
  have hdV : d ∈ V := (hcert.cheap_mem_V hdL).1
  have hdc : d ≠ c := (hcert.cheap_mem_V hdL).2
  have hcV : c ∈ V := hcert.distinguished_mem
  have hnow_u : now < u := harrival.trans hbeta
  -- the extra cheap candidate: the old flagged schedule at `d` stays put
  have hextra : Reaches start (alpha :: processed) u (m + 1) (V \ {d, c}) := by
    have hold := hcert.flagged d hdL (by rw [hq]; simp)
    rw [show V \ ({c, d} : Finset Page) = V \ {d, c} by rw [Finset.pair_comm]] at hold
    exact hold.mono_now hnow_u.le
  refine ⟨hdV, ?_, ⟨c, Finset.mem_insert_self _ _⟩, ?_, hpage, hbeta.le, hopen, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_erase.mpr ⟨hdc.symm, hcV⟩
    · obtain ⟨hzV, _, hzd⟩ := mem_diff_pair.mp hz
      exact Finset.mem_erase.mpr ⟨hzd, hzV⟩
  · intro y hy
    simp only [Option.mem_def, Option.some.injEq] at hy
    rw [← hy]
    exact Finset.mem_insert_self _ _
  · intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hcert.alpha_arrival.trans hnow_u.le
    · exact (hcert.processed_before w hw).trans hnow_u.le
  · intro z hz
    have hzV : z ∈ V := Finset.mem_of_mem_erase hz
    have hzd : z ≠ d := Finset.ne_of_mem_erase hz
    by_cases hzc : z = c
    · rw [hzc]; exact hround
    · exact (hcheap z (mem_diff_pair.mpr ⟨hzV, hzc, hzd⟩)).mono_cost (Nat.le_succ _)
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hextra
    · exact hcheap z hz
  · intro z hz hmark
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact absurd rfl hmark
    · exact hflagged z hz

/-! ## What the certificate is for -/

/-- **The certificate's payoff**, the draft's `OPT ≤ m_T + 1`: at any
checkpoint there is a schedule of cost at most `m + 1` that has served every
processed request inside its window *and* the distinguished request too. -/
theorem exists_final_schedule (hcert : Certificate V start processed alpha c L q m now)
    {z : Page} (hz : z ∈ L) (hne : (V \ {c, z}).Nonempty) :
    ∃ (t : Time) (cfg : Finset Page), Reaches start (alpha :: processed) t (m + 1) cfg := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨hyV, hyc, hyz⟩ := mem_diff_pair.mp hy
  obtain ⟨t, hnow_t, ht_deadline⟩ := exists_between hcert.alpha_open
  refine ⟨t, _, (hcert.cheap z hz).step_serving ⟨t, c, y⟩ alpha hnow_t hy ?_
    (fun w hw => (hcert.processed_before w hw).trans hnow_t.le)
    hcert.alpha_page.symm (hcert.alpha_arrival.trans hnow_t.le) ht_deadline.le⟩
  exact fun h => (mem_diff_pair.mp h).2.1 rfl

/-- **The certificate at the start.**  Two uncovered nodes `c` and `d`, a
request pending at `c`, cheap set `{d}` marked, and budget zero: every
background candidate is one move away, and no flag is promised.  This is the
drafts' initialization, and it shows the invariant is not vacuous. -/
theorem initial {c d : Page} (hc : c ∈ V) (hd : d ∈ V) (hcd : c ≠ d)
    {alpha : Window Page} (hpage : alpha.page = c) (harrival : alpha.arrival ≤ now)
    (hopen : now < alpha.deadline) :
    Certificate V (V \ {c, d}) [] alpha c {d} (some d) 0 now := by
  have hdV : d ∈ V := hd
  refine ⟨hc, ?_, ⟨d, by simp⟩, ?_, hpage, harrival, hopen, by simp, ?_, ?_, ?_⟩
  · intro z hz
    rw [Finset.mem_singleton] at hz
    exact hz ▸ Finset.mem_erase.mpr ⟨hcd.symm, hd⟩
  · intro y hy
    simp only [Option.mem_def, Option.some.injEq] at hy
    simp [hy]
  · -- background: one move reaches every candidate
    intro z hz
    have hzV : z ∈ V := Finset.mem_of_mem_erase hz
    have hzc : z ≠ c := Finset.ne_of_mem_erase hz
    by_cases hzd : z = d
    · refine ⟨[], trivial, List.Pairwise.nil, by simp, by simp, by simp, ?_⟩
      rw [hzd]
      rfl
    · refine ⟨[⟨now, d, z⟩], ⟨mem_diff_pair.mpr ⟨hzV, hzc, hzd⟩,
        fun h => (mem_diff_pair.mp h).2.2 rfl, trivial⟩,
        List.pairwise_singleton _ _, by simp, by simp, by simp, ?_⟩
      simpa [cacheAfter] using applyMove_pair hd hcd.symm (fun heq => hzd heq.symm) now
  · -- cheap: the initial configuration itself
    intro z hz
    rw [Finset.mem_singleton] at hz
    exact ⟨[], trivial, List.Pairwise.nil, by simp, by simp, by simp, by rw [hz]; rfl⟩
  · -- flagged: nothing is promised, since the mark is on the only candidate
    intro z hz hmark
    rw [Finset.mem_singleton] at hz
    exact absurd (by rw [hz]) hmark

end Certificate

end
end PagingWithDelay.DeadlineLowerBound
