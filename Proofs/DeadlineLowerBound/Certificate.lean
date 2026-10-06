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
  by_cases hyf : y = f
  · subst hyf; simp [applyMove, hf, hfp, hfe]
  · simp [applyMove, hyf]; tauto

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
  have h := hcert.cheap_subset hz
  exact ⟨Finset.mem_of_mem_erase h, Finset.ne_of_mem_erase h⟩

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
  obtain ⟨hax, haL⟩ := Finset.mem_erase.mp ha
  obtain ⟨hxc, hxV⟩ := Finset.mem_erase.mp hx
  have hnow_u : now < u := harrival.trans_le hu
  have harrivals : ∀ w ∈ gamma :: processed, w.arrival ≤ u :=
    List.forall_mem_cons.mpr ⟨hu, fun w hw => (hcert.processed_before w hw).trans hnow_u.le⟩
  -- a schedule whose index is not `x` is sitting on `x`, so it serves `gamma`
  -- without moving
  have hsits : ∀ z, z ≠ x → gamma.page ∈ V \ {c, z} := fun z hzx =>
    hpage ▸ mem_diff_pair.mpr ⟨hxV, hxc, fun heq => hzx heq.symm⟩
  refine ⟨hcert.distinguished_mem, (Finset.erase_subset _ _).trans hcert.cheap_subset,
    ⟨a, ha⟩, ?_, hcert.alpha_page, hcert.alpha_arrival.trans hnow_u.le, hopen, harrivals, ?_, ?_, ?_⟩
  · intro y hy
    split_ifs at hy with hq
    · simp at hy
    · exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hq hy, hcert.mark_mem y hy⟩
  · -- background: rebuild every candidate from the cheap schedule at `a`
    intro z hz
    obtain ⟨hzc, hzV⟩ := Finset.mem_erase.mp hz
    have hbase := (hcert.cheap a haL).serves_of_mem gamma (hsits a hax) harrival
    by_cases hza : z = a
    · exact hza ▸ (hbase.mono_now hnow_u.le).mono_cost m.le_succ
    · have hstep := hbase.step ⟨u, a, z⟩ hnow_u (mem_diff_pair.mpr ⟨hzV, hzc, hza⟩)
        (fun h => (mem_diff_pair.mp h).2.2 rfl) harrivals
      rwa [applyMove_pair (hcert.cheap_mem_V haL).1 (hcert.cheap_mem_V haL).2 (Ne.symm hza)]
        at hstep
  · -- cheap: the surviving candidates keep their schedules
    intro z hz
    obtain ⟨hzx, hzL⟩ := Finset.mem_erase.mp hz
    exact ((hcert.cheap z hzL).serves_of_mem gamma (hsits z hzx) harrival).mono_now hnow_u.le
  · -- flagged: likewise, and they keep their service of `alpha`
    intro z hz hq'
    obtain ⟨hzx, hzL⟩ := Finset.mem_erase.mp hz
    have hqz : q ≠ some z := by
      split_ifs at hq' with hq
      · simpa [hq] using Ne.symm hzx
      · exact hq'
    exact (((hcert.flagged z hzL hqz).serves_of_mem gamma (hsits z hzx) harrival).mono_now
      hnow_u.le).subset fun _ hw => (List.Perm.swap _ _ _).subset hw

/-! ## Operation (P): paying, and promoting the reserve request

The payment is where the mark does its work.  Both branches refill the cheap
set from `V \ {c, d}`, and the long branch — available exactly when no cheap
candidate lacks a flagged counterpart — keeps the old flagged schedule at `d`
as one extra cheap candidate, at the price of leaving *it* unflagged.
-/

variable {d : Page} {beta : Window Page} {u : Time}

/-- What the payment builds, shared by its two branches: the new checkpoint is
after every processed request, every background candidate is reached (the one
indexed by the old distinguished node by the draft's round trip), and the new
cheap family `V \ {c, d}` comes with its flagged counterparts. -/
private theorem pay_pieces (hcert : Certificate V start processed alpha c L q m now)
    (hL : L = {d}) (hK : (V \ {c, d}).Nonempty)
    (hpage : beta.page = d) (harrival : now < beta.arrival)
    (hbeta : beta.arrival < u) (halpha : u ≤ alpha.deadline) :
    (∀ w ∈ alpha :: processed, w.arrival ≤ u) ∧
      (∀ z ∈ V.erase d, Reaches start (alpha :: processed) u (m + 2) (V \ {d, z})) ∧
      (∀ z ∈ V \ {c, d}, Reaches start (alpha :: processed) u (m + 1) (V \ {d, z})) ∧
      (∀ z ∈ V \ {c, d},
        Reaches start (beta :: alpha :: processed) u (m + 2) (V \ {d, z})) := by
  have hdL : d ∈ L := by rw [hL]; simp
  obtain ⟨hdV, hdc⟩ := hcert.cheap_mem_V hdL
  have hcV : c ∈ V := hcert.distinguished_mem
  have hnow_u : now < u := harrival.trans hbeta
  have hcnot : c ∉ V \ ({c, d} : Finset Page) := fun h => (mem_diff_pair.mp h).2.1 rfl
  have hbefore : ∀ t, now ≤ t → ∀ w ∈ alpha :: processed, w.arrival ≤ t := fun t ht =>
    List.forall_mem_cons.mpr ⟨hcert.alpha_arrival.trans ht,
      fun w hw => (hcert.processed_before w hw).trans ht⟩
  -- from the old cheap schedule at `d`, fetch `c` at any time `t` in `alpha`'s window
  have hout : ∀ t, now < t → t ≤ alpha.deadline → ∀ z ∈ V \ ({c, d} : Finset Page),
      Reaches start (alpha :: processed) t (m + 1) (V \ {d, z}) := by
    intro t hnow_t ht z hz
    have hstep := (hcert.cheap d hdL).step_serving ⟨t, c, z⟩ alpha hnow_t hz hcnot
      (fun w hw => (hcert.processed_before w hw).trans hnow_t.le) hcert.alpha_page.symm
      (hcert.alpha_arrival.trans hnow_t.le) ht
    rwa [Finset.pair_comm,
      applyMove_pair hcV hdc.symm (fun heq => (mem_diff_pair.mp hz).2.1 heq.symm)] at hstep
  refine ⟨hbefore u hnow_u.le, fun z hz => ?_, hout u hnow_u halpha, fun z hz => ?_⟩
  · -- background
    obtain ⟨hzd, hzV⟩ := Finset.mem_erase.mp hz
    by_cases hzc : z = c
    · -- the round trip: fetch `c` evicting some `w`, then fetch `w` back
      subst hzc
      obtain ⟨w, hw⟩ := hK
      obtain ⟨hwV, hwc, hwd⟩ := mem_diff_pair.mp hw
      obtain ⟨t₁, hnow_t₁, ht₁_u⟩ := exists_between hnow_u
      have hback := (hout t₁ hnow_t₁ (ht₁_u.le.trans halpha) w hw).step ⟨u, w, z⟩ ht₁_u
        (mem_diff_pair.mpr ⟨hcV, hdc.symm, fun heq => hwc heq.symm⟩)
        (fun h => (mem_diff_pair.mp h).2.2 rfl) (hbefore u hnow_u.le)
      rwa [applyMove_pair hwV hwd hwc u] at hback
    · exact (hout u hnow_u halpha z (mem_diff_pair.mpr ⟨hzV, hzc, hzd⟩)).mono_cost
        m.succ.le_succ
  · -- flagged: from the background schedule at `z`, which is sitting on `d`
    -- when `beta` arrives, fetch `c`
    obtain ⟨hzV, hzc, hzd⟩ := mem_diff_pair.mp hz
    have hsits : beta.page ∈ V \ ({c, z} : Finset Page) :=
      hpage ▸ mem_diff_pair.mpr ⟨hdV, hdc, fun heq => hzd heq.symm⟩
    have hstep := ((hcert.background z (Finset.mem_erase.mpr ⟨hzc, hzV⟩)).serves_of_mem
      beta hsits harrival).step_serving ⟨u, c, d⟩ alpha hnow_u (hpage ▸ hsits)
      (fun h => (mem_diff_pair.mp h).2.1 rfl)
      (List.forall_mem_cons.mpr
        ⟨hbeta.le, fun w hw => (hcert.processed_before w hw).trans hnow_u.le⟩)
      hcert.alpha_page.symm (hcert.alpha_arrival.trans hnow_u.le) halpha
    rw [Finset.pair_comm, applyMove_pair hcV (fun heq => hzc heq.symm) hdc.symm u,
      Finset.pair_comm] at hstep
    exact hstep.subset fun _ hw => (List.Perm.swap _ _ _).subset hw

/-- **Operation (P), short payment.**  The mark sits on the last cheap
candidate, so the old flagged family is empty and the new cheap set is just
`V \ {c, d}` — `k` candidates, all of them flagged.

The mark hypothesis `_hq` is not used: the short payment is available whatever
the mark is.  It is kept so that the transitions here match
`PhaseCount.Step.payShort` one for one. -/
theorem pay_short (hcert : Certificate V start processed alpha c L q m now)
    (hL : L = {d}) (_hq : q = some d) (hK : (V \ {c, d}).Nonempty)
    (hpage : beta.page = d) (harrival : now < beta.arrival)
    (hbeta : beta.arrival < u) (halpha : u ≤ alpha.deadline) (hopen : u < beta.deadline) :
    Certificate V start (alpha :: processed) beta d (V \ {c, d}) none (m + 1) u := by
  obtain ⟨hbefore, hbackground, hcheap, hflagged⟩ :=
    pay_pieces hcert hL hK hpage harrival hbeta halpha
  refine ⟨(hcert.cheap_mem_V (hL ▸ Finset.mem_singleton_self d)).1, fun z hz => ?_, hK, by simp,
    hpage, hbeta.le, hopen, hbefore, hbackground, hcheap, fun z hz _ => hflagged z hz⟩
  obtain ⟨hzV, _, hzd⟩ := mem_diff_pair.mp hz
  exact Finset.mem_erase.mpr ⟨hzd, hzV⟩

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
  obtain ⟨hbefore, hbackground, hcheap, hflagged⟩ :=
    pay_pieces hcert hL hK hpage harrival hbeta halpha
  have hdL : d ∈ L := by rw [hL]; simp
  obtain ⟨hdV, hdc⟩ := hcert.cheap_mem_V hdL
  refine ⟨hdV, ?_, Finset.insert_nonempty _ _, by simp, hpage, hbeta.le, hopen, hbefore,
    hbackground, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_erase.mpr ⟨hdc.symm, hcert.distinguished_mem⟩
    · obtain ⟨hzV, _, hzd⟩ := mem_diff_pair.mp hz
      exact Finset.mem_erase.mpr ⟨hzd, hzV⟩
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · -- the extra cheap candidate: the old flagged schedule at `d` stays put
      have hold := hcert.flagged d hdL (by simp [hq])
      rw [Finset.pair_comm] at hold
      exact hold.mono_now (harrival.trans hbeta).le
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
  refine ⟨hc, by simpa [Finset.mem_erase] using ⟨Ne.symm hcd, hd⟩, ⟨d, by simp⟩, by simp,
    hpage, harrival, hopen, by simp, ?_, ?_, ?_⟩
  · -- background: one move reaches every candidate
    intro z hz
    obtain ⟨hzc, hzV⟩ := Finset.mem_erase.mp hz
    by_cases hzd : z = d
    · exact ⟨[], trivial, List.Pairwise.nil, by simp, by simp, by simp, by rw [hzd]; rfl⟩
    · refine ⟨[⟨now, d, z⟩], ⟨mem_diff_pair.mpr ⟨hzV, hzc, hzd⟩,
        fun h => (mem_diff_pair.mp h).2.2 rfl, trivial⟩,
        List.pairwise_singleton _ _, by simp, by simp, by simp, ?_⟩
      simpa [cacheAfter] using applyMove_pair hd hcd.symm (fun heq => hzd heq.symm) now
  · -- cheap: the initial configuration itself
    intro z hz
    exact ⟨[], trivial, List.Pairwise.nil, by simp, by simp, by simp, by simp_all⟩
  · -- flagged: nothing is promised, since the mark is on the only candidate
    intro z hz hmark
    exact absurd (by simp_all) hmark

end Certificate

end
end PagingWithDelay.DeadlineLowerBound
