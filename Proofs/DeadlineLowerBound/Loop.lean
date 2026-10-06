import Proofs.DeadlineLowerBound.Online
import Proofs.DeadlineLowerBound.Bridge
import Proofs.DeadlineLowerBound.PhaseCount

/-!
# The adaptive construction

This is the drafts' adversary, run against an arbitrary online
algorithm.  A `Run` carries, side by side,

* the input released so far, every request of it a miss on arrival and the
  requests pairwise separated, so that `Online.length_le_totalCost` charges one
  unit of the algorithm's cost to each of them;
* the offline certificate of `Certificate.lean` for those same requests; and
* the run of `PhaseCount.lean` that led to the certificate's state, which
  bounds its budget.

`Run.advance` performs one operation: it looks at the algorithm's cache,
releases one request at a page the algorithm does not hold, and applies the
matching certificate operation — the payment when the cheap set is a singleton
whose page the algorithm has dropped, an auxiliary processing step otherwise.

## Timing

Each request is free until its deadline and has accrued a unit of delay at the
end of its *charging window*.  The invariants keep two clocks apart:

* `clock` — nothing has arrived after it, nothing will arrive at or before it,
  and every charging window has closed by it *except* the distinguished
  request's;
* `checkpoint` — the certificate's clock, which may lag behind.

A phase squeezes its auxiliary requests into the distinguished request's
window, and the payment closes that window: it is taken at `checkpoint =
alpha.deadline`, and the clock then moves to `alpha.deadline + 1`, past the end
of the distinguished request's charging window.  That is what keeps the
separation: within a phase the auxiliary pages differ from the distinguished
page, and across phases the windows are disjoint.
-/

namespace PagingWithDelay.DeadlineLowerBound

open Finset

noncomputable section

variable {Page : Type*} [DecidableEq Page]

/-- The request the adversary releases: free until `deadline`, and carrying a
whole unit of delay at `chargeEnd`.

`Model.lean` has no hard deadlines, so the stand-in is a curve that stays at
zero until the deadline and then grows at rate `1 / (chargeEnd - deadline)`.
A continuous curve charges `rate * overshoot`, so charging a whole unit within
an overshoot of `ε` needs `rate ≥ 1 / ε`; that is what lets the construction
squeeze arbitrarily many chargeable requests into a bounded interval, which the
drafts get for free from hard deadlines. -/
def releaseRequest (page : Page) (arrival deadline chargeEnd : Time) (h : deadline < chargeEnd) :
    Request Page where
  page := page
  arrival := arrival
  delay := fun wait => (wait - (deadline - arrival)) / (chargeEnd - deadline)
  delay_continuous := (continuous_id.sub continuous_const).div_const _
  delay_mono := fun _ _ hle => by dsimp only; gcongr
  delay_zero := by simp
  delay_unbounded := fun bound => ⟨(deadline - arrival) + bound * (chargeEnd - deadline), by
    rw [add_tsub_cancel_left, mul_div_cancel_right₀ _ (tsub_pos_of_lt h).ne']⟩

omit [DecidableEq Page] in
theorem releaseRequest_free (page : Page) {arrival deadline chargeEnd : Time}
    (h : deadline < chargeEnd) :
    (releaseRequest page arrival deadline chargeEnd h).delay (deadline - arrival) = 0 := by
  simp [releaseRequest]

omit [DecidableEq Page] in
theorem releaseRequest_penalty (page : Page) {arrival deadline chargeEnd : Time}
    (h : deadline < chargeEnd) (harrival : arrival ≤ deadline) :
    1 ≤ (releaseRequest page arrival deadline chargeEnd h).delay (chargeEnd - arrival) := by
  simp [releaseRequest, tsub_tsub_tsub_cancel_right harrival, (tsub_pos_of_lt h).ne']

/-- The state of the adaptive construction after finitely many operations,
started with distinguished node `c` and cheap set `{d}`. -/
structure Run (algorithm : Algorithm Page) (k : ℕ) (V : Finset Page) (c d : Page) where
  /-- The requests released so far. -/
  input : Instance Page
  size : input.cacheSize = k
  /-- The initial cache is drawn from the universe. -/
  initialPages : ∀ page ∈ input.initialCache, page ∈ V
  /-- The certificate starts from the instance's initial cache, so the
  comparator needs no start-up fetches. -/
  startEq : input.initialCache.toFinset = V \ {c, d}
  /-- The deadline and the charging window of each released request. -/
  deadline : Request Page → Time
  chargeWindow : Request Page → Time
  /-- The certificate's combinatorial state, reached in `steps` operations. -/
  steps : ℕ
  state : PhaseCount.Certificate Page
  history : PhaseCount.Run V (PhaseCount.initial c d) steps state
  stateValid : state.Valid V k
  lengthEq : input.requests.length = steps + 1
  /-- The adversary's clock and the certificate's checkpoint. -/
  clock : Time
  checkpoint : Time
  processed : List (Window Page)
  alpha : Window Page
  cert : Certificate V (V \ {c, d}) processed alpha state.distinguished state.cheap state.mark
    state.budget checkpoint
  clockPos : 0 < clock
  checkpointLe : checkpoint ≤ clock
  alphaLate : clock < alpha.deadline
  arrivals : ∀ request ∈ input.requests, request.arrival ≤ clock
  pages : ∀ request ∈ input.requests, request.page ∈ V
  /-- Every request was a miss when it arrived. -/
  misses : ∀ request ∈ input.requests,
    request.page ∉ (algorithm input).cacheBefore request.arrival
  penalty : ∀ request ∈ input.requests, 1 ≤ request.delay (chargeWindow request)
  free : ∀ request ∈ input.requests, request.delay (deadline request - request.arrival) = 0
  ordered : input.requests.Pairwise fun first second =>
    first.page ≠ second.page ∨ first.arrival + chargeWindow first < second.arrival
  /-- Every charging window has closed, except the distinguished request's. -/
  closed : ∀ request ∈ input.requests,
    request.arrival + chargeWindow request ≤ clock ∨ request.page = state.distinguished
  /-- The distinguished request's charging window closes just after its deadline. -/
  alphaClosed : ∀ request ∈ input.requests, request.page = state.distinguished →
    request.arrival + chargeWindow request ≤ alpha.deadline + 1
  link : ∀ request ∈ input.requests,
    (⟨request.page, request.arrival, deadline request⟩ : Window Page) ∈ alpha :: processed

omit [DecidableEq Page] in
theorem forall_mem_appendRequest {input : Instance Page} {request : Request Page}
    {hlast : ∀ other ∈ input.requests, other.arrival ≤ request.arrival}
    {P : Request Page → Prop}
    (hold : ∀ other ∈ input.requests, P other) (hnew : P request) :
    ∀ other ∈ (input.appendRequest request hlast).requests, P other :=
  List.forall_mem_append.mpr ⟨hold, List.forall_mem_singleton.mpr hnew⟩

/-! ## Starting the construction -/

/-- Before time `0` every schedule still holds its initial cache. -/
theorem cacheBefore_zero (schedule : Schedule Page) :
    schedule.cacheBefore 0 = schedule.initialCache := by
  unfold Schedule.cacheBefore
  generalize schedule.initialCache = init
  induction schedule.events generalizing init with
  | nil => rfl
  | cons event rest ih => simpa only [List.foldl_cons, not_lt_zero', if_false] using ih init

/-- The construction starts, as in the write-up, at time `0`: the initial
cache is `k` pages of the universe, `c` and `d` are the two pages outside it,
and the first distinguished request is released at `c` at time `0`, before the
algorithm can act.  The certificate therefore starts from the initial cache
itself, `V \ {c, d}`. -/
theorem exists_initial (algorithm : Algorithm Page) {k : ℕ} (hk : 1 ≤ k) {V : Finset Page}
    (hcard : V.card = k + 2) :
    ∃ (c d : Page), c ∈ V ∧ d ∈ V ∧ c ≠ d ∧
      ∃ run : Run algorithm k V c d, run.steps = 0 := by
  classical
  -- the initial cache: any `k` pages of the universe
  set empty : Instance Page := ⟨k, V.toList.take k, [], List.Pairwise.nil, hk,
    (Finset.nodup_toList V).sublist (List.take_sublist _ _), by simp [hcard]⟩
  have hinitial : ∀ page ∈ empty.initialCache, page ∈ V :=
    fun page hpage => Finset.mem_toList.mp (List.mem_of_mem_take hpage)
  have hsub : empty.initialCache.toFinset ⊆ V :=
    fun page hpage => hinitial page (List.mem_toFinset.mp hpage)
  have hcardInit : empty.initialCache.toFinset.card = k := by
    rw [List.toFinset_card_of_nodup empty.initialCache_nodup, empty.initialCache_full]
  -- the two pages outside the initial cache
  have hcardOut : (V \ empty.initialCache.toFinset).card = 2 := by
    have := Finset.card_sdiff_add_card_eq_card hsub
    omega
  obtain ⟨c, d, hcd, hout⟩ := Finset.card_eq_two.mp hcardOut
  have hcOut : c ∈ V \ empty.initialCache.toFinset := by rw [hout]; simp
  have hdOut : d ∈ V \ empty.initialCache.toFinset := by rw [hout]; simp
  obtain ⟨hcV, hcmiss⟩ := Finset.mem_sdiff.mp hcOut
  have hdV : d ∈ V := (Finset.mem_sdiff.mp hdOut).1
  -- the first distinguished request, at time `0`
  set alpha : Request Page := releaseRequest c 0 2 3 (by norm_num) with halpha_def
  have halpha : ∀ r ∈ empty.requests, r.arrival ≤ alpha.arrival := by simp [empty]
  have hmiss : alpha.page ∉ (algorithm (empty.appendRequest alpha halpha)).cacheBefore 0 := by
    rw [cacheBefore_zero, (algorithm.feasible _).initialCache]
    exact hcmiss
  have hsingle : ∀ {P : Request Page → Prop}, P alpha →
      ∀ request ∈ (empty.appendRequest alpha halpha).requests, P request :=
    fun hP => forall_mem_appendRequest (by simp [empty]) hP
  refine ⟨c, d, hcV, hdV, hcd,
    { input := empty.appendRequest alpha halpha
      size := rfl
      initialPages := hinitial
      startEq := by rw [← hout, Finset.sdiff_sdiff_eq_self hsub]; rfl
      deadline := fun _ => 2
      chargeWindow := fun _ => 3
      steps := 0
      state := PhaseCount.initial c d
      history := .refl _
      stateValid := PhaseCount.initial_valid hcV hdV hcd
      lengthEq := rfl
      clock := 1
      checkpoint := 0
      processed := []
      alpha := ⟨c, 0, 2⟩
      cert := Certificate.initial hcV hdV hcd rfl le_rfl (by norm_num)
      clockPos := one_pos
      checkpointLe := zero_le_one
      alphaLate := one_lt_two
      arrivals := hsingle zero_le_one
      pages := hsingle hcV
      misses := hsingle hmiss
      penalty := hsingle (by simpa using releaseRequest_penalty c (arrival := 0) _ (zero_le _))
      free := hsingle (releaseRequest_free c _)
      ordered := List.pairwise_singleton _ _
      closed := hsingle (Or.inr rfl)
      alphaClosed := hsingle fun _ => by norm_num [halpha_def, releaseRequest]
      link := hsingle (List.mem_singleton_self _) }, rfl⟩

/-! ## One operation -/

/-- **One operation, given the request and the certificate operation.**  The
request at `p` arrives at `a`, after the clock, is free until `w` and has
accrued a unit of delay at `e`.  The invariants about the input itself are
maintained generically; the hypotheses are the ones about the new certificate,
the new clock and the closing of charging windows. -/
theorem Run.extend {algorithm : Algorithm Page} (online : algorithm.Online)
    {k : ℕ} (hk : 1 ≤ k) {V : Finset Page} (hcard : V.card = k + 2) {c d : Page}
    (run : Run algorithm k V c d) {p : Page} {a w e : Time}
    (hta : run.clock < a) (haw : a < w) (hwe : w < e) (hpV : p ∈ V)
    (hpc : p ≠ run.state.distinguished) (hmiss : p ∉ (algorithm run.input).cacheBefore a)
    {state : PhaseCount.Certificate Page} (hstep : PhaseCount.Step V run.state state)
    {clock checkpoint : Time} {processed : List (Window Page)} {alpha : Window Page}
    (cert : Certificate V (V \ {c, d}) processed alpha state.distinguished state.cheap
      state.mark state.budget checkpoint)
    (hclock : a ≤ clock) (hcheckpoint : checkpoint ≤ clock) (halpha : clock < alpha.deadline)
    (hlink : ∀ window ∈ run.alpha :: run.processed, window ∈ alpha :: processed)
    (hlinkNew : (⟨p, a, w⟩ : Window Page) ∈ alpha :: processed)
    (hclosed : ∀ request ∈ run.input.requests,
      request.arrival + run.chargeWindow request ≤ clock ∨ request.page = state.distinguished)
    (hclosedNew : e ≤ clock ∨ p = state.distinguished)
    (halphaClosed : ∀ request ∈ run.input.requests, request.page = state.distinguished →
      request.arrival + run.chargeWindow request ≤ alpha.deadline + 1)
    (halphaClosedNew : p = state.distinguished → e ≤ alpha.deadline + 1) :
    ∃ next : Run algorithm k V c d, next.steps = run.steps + 1 := by
  classical
  have hold : ∀ request ∈ run.input.requests, request.arrival ≠ a :=
    fun request hrequest heq => (run.arrivals request hrequest).not_gt (heq ▸ hta)
  have hearlier : ∀ request ∈ run.input.requests, request.arrival ≤ a :=
    fun request hrequest => (run.arrivals request hrequest).trans hta.le
  have hae : a + (e - a) = e := add_tsub_cancel_of_le (haw.trans hwe).le
  set request := releaseRequest p a w e hwe
  set deadline : Request Page → Time := fun other =>
    if other.arrival = a then w else run.deadline other with hdeadline
  set chargeWindow : Request Page → Time := fun other =>
    if other.arrival = a then e - a else run.chargeWindow other with hchargeWindow
  have hdl : ∀ other ∈ run.input.requests, deadline other = run.deadline other :=
    fun other hother => if_neg (hold other hother)
  have hcw : ∀ other ∈ run.input.requests, chargeWindow other = run.chargeWindow other :=
    fun other hother => if_neg (hold other hother)
  have hdlNew : deadline request = w := if_pos rfl
  have hcwNew : chargeWindow request = e - a := if_pos rfl
  refine ⟨{
    input := run.input.appendRequest request hearlier
    size := run.size
    initialPages := run.initialPages
    startEq := run.startEq
    deadline := deadline
    chargeWindow := chargeWindow
    steps := run.steps + 1
    state := state
    history := run.history.tail hstep
    stateValid := PhaseCount.Step.valid hcard hk run.stateValid hstep
    lengthEq := by simp [Instance.appendRequest, run.lengthEq]
    clock := clock
    checkpoint := checkpoint
    processed := processed
    alpha := alpha
    cert := cert
    clockPos := run.clockPos.trans (hta.trans_le hclock)
    checkpointLe := hcheckpoint
    alphaLate := halpha
    arrivals := forall_mem_appendRequest
      (fun other hother => (hearlier other hother).trans hclock) hclock
    pages := forall_mem_appendRequest run.pages hpV
    misses := appendRequest_misses online run.input request hearlier run.misses hmiss
    penalty := forall_mem_appendRequest
      (fun other hother => hcw other hother ▸ run.penalty other hother)
      (hcwNew ▸ releaseRequest_penalty p hwe haw.le)
    free := forall_mem_appendRequest
      (fun other hother => hdl other hother ▸ run.free other hother)
      (hdlNew ▸ releaseRequest_free p hwe)
    ordered := List.pairwise_append.mpr ⟨run.ordered.imp_of_mem fun hfirst _ h => by
        rwa [hcw _ hfirst], List.pairwise_singleton _ _, fun first hfirst second hsecond => by
        rw [List.mem_singleton.mp hsecond, hcw first hfirst]
        rcases run.closed first hfirst with hclosedFirst | hpageFirst
        · exact Or.inr (hclosedFirst.trans_lt hta)
        · exact Or.inl (hpageFirst ▸ hpc.symm)⟩
    closed := forall_mem_appendRequest
      (fun other hother => hcw other hother ▸ hclosed other hother)
      (show a + chargeWindow request ≤ clock ∨ p = state.distinguished by rwa [hcwNew, hae])
    alphaClosed := forall_mem_appendRequest
      (fun other hother => hcw other hother ▸ halphaClosed other hother)
      (show p = state.distinguished → a + chargeWindow request ≤ alpha.deadline + 1 by
        rwa [hcwNew, hae])
    link := forall_mem_appendRequest
      (fun other hother => hdl other hother ▸ hlink _ (run.link other hother))
      (hdlNew ▸ hlinkNew) }, rfl⟩

/-- **One operation of the construction.**  The adversary looks at the
algorithm's cache just before the next arrival and releases one request there:
the reserve request on the last cheap candidate when the algorithm has dropped
it — which lets the certificate pay — and otherwise an auxiliary request, which
the certificate processes for free. -/
theorem Run.advance {algorithm : Algorithm Page} (online : algorithm.Online)
    {k : ℕ} (hk : 1 ≤ k) {V : Finset Page} (hcard : V.card = k + 2) {c d : Page}
    (run : Run algorithm k V c d) :
    ∃ next : Run algorithm k V c d, next.steps = run.steps + 1 := by
  obtain ⟨a, hta, haD⟩ := exists_between run.alphaLate
  have harrival : run.checkpoint < a := run.checkpointLe.trans_lt hta
  set D : Time := run.alpha.deadline
  by_cases hpay : ∃ p, run.state.cheap = {p} ∧ p ∉ (algorithm run.input).cacheBefore a
  · -- the payment: release the reserve request at `p`, free until `D + 2`, then pay at `D`
    obtain ⟨p, hcheap, hpmiss⟩ := hpay
    obtain ⟨hpV, hcp⟩ := run.stateValid.pay_facts hcheap
    have hK := PhaseCount.refill_nonempty hcard hk run.stateValid.distinguished_mem hpV hcp
    obtain ⟨state, hstep, hdist, hcert⟩ : ∃ state, PhaseCount.Step V run.state state ∧
        state.distinguished = p ∧
        Certificate V (V \ {c, d}) (run.alpha :: run.processed) ⟨p, a, D + 2⟩
          state.distinguished state.cheap state.mark state.budget D := by
      rcases PhaseCount.pay_cases run.stateValid hcheap with hmark | hmark
      · exact ⟨_, .payShort run.state p hcheap hmark, rfl,
          run.cert.pay_short hcheap hmark hK rfl harrival haD le_rfl (by simp)⟩
      · exact ⟨_, .payLong run.state p hcheap hmark, rfl,
          run.cert.pay_long hcheap hmark hK rfl harrival haD le_rfl (by simp)⟩
    -- every old charging window has closed by `D + 1`
    have hshut : ∀ request ∈ run.input.requests,
        request.arrival + run.chargeWindow request ≤ D + 1 :=
      fun request hrequest => (run.closed request hrequest).elim
        (fun h => h.trans (run.alphaLate.le.trans le_self_add)) (run.alphaClosed request hrequest)
    -- free until `D + 2`, a unit of delay at `D + 3`; the clock moves to `D + 1`, the
    -- checkpoint to `D`, and only the new, distinguished request's window stays open
    exact run.extend online hk hcard hta (haD.trans_le le_self_add) (lt_add_one (D + 2)) hpV
      (Ne.symm hcp) hpmiss hstep hcert (haD.le.trans le_self_add) le_self_add
      (by simp only [D]; norm_num) (fun _ => List.mem_cons_of_mem _) List.mem_cons_self
      (fun request hrequest => Or.inl (hshut request hrequest)) (Or.inr hdist.symm)
      (fun request hrequest _ => (hshut request hrequest).trans (by norm_num)) fun _ => le_rfl
  · -- an auxiliary request: the algorithm still holds the last cheap candidate
    push_neg at hpay
    obtain ⟨x, hxV, hxc, hxmiss⟩ := exists_uncovered_ne (algorithm run.input)
      (algorithm.feasible run.input) run.size hcard.ge a run.state.distinguished
    have hnonempty : (run.state.cheap.erase x).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, Finset.erase_eq_empty_iff]
      rintro (h | h)
      · exact run.stateValid.nonempty.ne_empty h
      · exact hxmiss (hpay x h)
    obtain ⟨w, haw, hwD⟩ := exists_between haD
    obtain ⟨e, hwe, heD⟩ := exists_between hwD
    have hae : a ≤ e := (haw.trans hwe).le
    -- free until `w`, a unit of delay at `e < D`; clock and checkpoint move to `e`
    exact run.extend online hk hcard hta haw hwe hxV hxc hxmiss
      (.process run.state x hxc hnonempty)
      (run.cert.process (Finset.mem_erase.mpr ⟨hxc, hxV⟩) hnonempty (gamma := ⟨x, a, w⟩) rfl
        harrival hae heD) hae le_rfl heD
      (fun _ h => by simp at h ⊢; tauto) (by simp)
      (fun request hrequest => (run.closed request hrequest).imp_left
        fun h => h.trans (hta.le.trans hae)) (Or.inl le_rfl) run.alphaClosed
      fun h => absurd h hxc

/-! ## Running the construction for as long as we like -/

/-- **The construction runs for any number of operations.** -/
theorem exists_run {algorithm : Algorithm Page} (online : algorithm.Online)
    {k : ℕ} (hk : 1 ≤ k) {V : Finset Page} (hcard : V.card = k + 2) (steps : ℕ) :
    ∃ (c d : Page), c ∈ V ∧ d ∈ V ∧ c ≠ d ∧
      ∃ run : Run algorithm k V c d, run.steps = steps := by
  induction steps with
  | zero => exact exists_initial algorithm hk hcard
  | succ previous ih =>
      obtain ⟨c, d, hc, hd, hcd, run, hsteps⟩ := ih
      obtain ⟨next, hnext⟩ := run.advance online hk hcard
      exact ⟨c, d, hc, hd, hcd, next, by rw [hnext, hsteps]⟩

end
end PagingWithDelay.DeadlineLowerBound
