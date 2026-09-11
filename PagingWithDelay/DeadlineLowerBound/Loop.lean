import PagingWithDelay.DeadlineLowerBound.Online
import PagingWithDelay.DeadlineLowerBound.Bridge
import PagingWithDelay.DeadlineLowerBound.PhaseCount

/-!
# The adaptive construction

This is the drafts' adversary, run against an arbitrary online feasible
algorithm.  A `Run` carries, side by side,

* the input released so far, every request of it a miss on arrival and the
  requests pairwise separated, so that `Online.length_le_totalCost` charges one
  unit of the algorithm's cost to each of them;
* the offline certificate of `Certificate.lean` for those same requests; and
* the potential of `PhaseCount.lean`, which bounds the certificate's budget.

`Run.advance` performs one operation: it looks at the algorithm's cache,
releases one request at a page the algorithm does not hold, and applies the
matching certificate operation — the payment when the cheap set is a singleton
whose page the algorithm has dropped, an auxiliary processing step otherwise.

## Timing

Each request is free until its deadline and has accrued a unit of delay one
overshoot later; its *charging window* runs from its arrival to that point.
The invariants keep two clocks apart:

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

/-- The request the adversary releases: free until `arrival + window`, and
carrying a whole unit of delay `overshoot` later. -/
def releaseRequest (page : Page) (arrival window overshoot : Time) (hover : 0 < overshoot) :
    Request Page :=
  deadlineRequest page arrival window (1 / overshoot) (by
    have : (0 : Time) < 1 / overshoot := by
      simpa using hover
    exact this)

omit [DecidableEq Page] in
@[simp] theorem releaseRequest_page (page : Page) (arrival window overshoot : Time)
    (hover : 0 < overshoot) : (releaseRequest page arrival window overshoot hover).page = page :=
  rfl

omit [DecidableEq Page] in
@[simp] theorem releaseRequest_arrival (page : Page) (arrival window overshoot : Time)
    (hover : 0 < overshoot) :
    (releaseRequest page arrival window overshoot hover).arrival = arrival := rfl

omit [DecidableEq Page] in
theorem releaseRequest_free (page : Page) (arrival window overshoot : Time)
    (hover : 0 < overshoot) :
    (releaseRequest page arrival window overshoot hover).delay
      ((arrival + window) - arrival) = 0 :=
  deadlineRequest_delay_window _ _ _ _ _

omit [DecidableEq Page] in
theorem releaseRequest_penalty (page : Page) (arrival window overshoot : Time)
    (hover : 0 < overshoot) :
    1 ≤ (releaseRequest page arrival window overshoot hover).delay (window + overshoot) := by
  refine deadlineRequest_delay_penalty _ _ _ _ _ _ ?_
  rw [div_mul_cancel₀ _ (ne_of_gt hover)]

/-- A request of the shape the adversary releases: free inside its window, then
growing at a fixed rate. -/
def IsDeadlineShaped (request : Request Page) : Prop :=
  ∃ (window rate : Time) (hrate : 0 < rate),
    request = deadlineRequest request.page request.arrival window rate hrate

omit [DecidableEq Page] in
/-- What a deadline-shaped request looks like, written out in `Model.lean`'s
own vocabulary: the delay curve is zero until `window` has elapsed and then
grows at a fixed positive rate. -/
theorem IsDeadlineShaped.exists_curve {request : Request Page} (shaped : IsDeadlineShaped request) :
    ∃ window rate : Time, 0 < rate ∧ ∀ wait : Time, request.delay wait = rate * (wait - window) := by
  obtain ⟨window, rate, hrate, heq⟩ := shaped
  refine ⟨window, rate, hrate, fun wait => ?_⟩
  rw [heq]
  rfl

omit [DecidableEq Page] in
theorem releaseRequest_shaped (page : Page) (arrival window overshoot : Time)
    (hover : 0 < overshoot) :
    IsDeadlineShaped (releaseRequest page arrival window overshoot hover) :=
  ⟨window, 1 / overshoot, by simpa using hover, rfl⟩

/-- The state of the adaptive construction after finitely many operations. -/
structure Run (algorithm : Algorithm Page) (k : ℕ) (V start : Finset Page) where
  /-- The requests released so far. -/
  input : Instance Page
  valid : input.Valid
  size : input.cacheSize = k
  /-- The deadline and the charging window of each released request. -/
  deadline : Request Page → Time
  chargeWindow : Request Page → Time
  /-- The certificate's combinatorial state. -/
  state : PhaseCount.Certificate Page
  stateValid : state.Valid V k
  /-- The adversary's clock and the certificate's checkpoint. -/
  clock : Time
  checkpoint : Time
  processed : List (Window Page)
  alpha : Window Page
  cert : Certificate V start processed alpha state.distinguished state.cheap state.mark
    state.budget checkpoint
  clockPos : 0 < clock
  checkpointLe : checkpoint ≤ clock
  alphaLate : clock < alpha.deadline
  positive : ∀ request ∈ input.requests, 0 < request.arrival
  arrivals : ∀ request ∈ input.requests, request.arrival ≤ clock
  /-- Every request was a miss when it arrived. -/
  shaped : ∀ request ∈ input.requests, IsDeadlineShaped request
  pages : ∀ request ∈ input.requests, request.page ∈ V
  misses : ∀ request ∈ input.requests,
    request.page ∉ (algorithm input valid).cacheBefore request.arrival
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
  /-- The number of certificate operations, and the potential bound behind the
  budget count. -/
  steps : ℕ
  potentialBound : (2 * k + 1) * state.budget + 2 ≤ 2 * steps + state.potential
  lengthEq : input.requests.length = steps + 1

/-! ## Starting the construction -/

/-- The construction starts by releasing the first distinguished request, at
time `1`, on a page the algorithm does not hold then. -/
theorem exists_initial (algorithm : Algorithm Page) (online : algorithm.Online)
    (feasible : algorithm.Feasible) {k : ℕ} (hk : 1 ≤ k) {V : Finset Page}
    (hcard : V.card = k + 2) :
    ∃ (c d : Page), c ∈ V ∧ d ∈ V ∧ c ≠ d ∧
      ∃ run : Run algorithm k V (V \ {c, d}), run.steps = 0 := by
  classical
  set empty : Instance Page := ⟨k, []⟩ with hempty
  have emptyValid : empty.Valid := ⟨List.Pairwise.nil, hk⟩
  -- two pages the algorithm does not hold just before time 1
  obtain ⟨c, hcmem, d, hdmem, hcd⟩ :=
    Finset.one_lt_card.mp (two_le_card_uncovered (algorithm empty emptyValid)
      (feasible.scheduleFeasible empty emptyValid) (show empty.cacheSize = k from rfl) hcard.ge 1)
  obtain ⟨hcV, hcmiss⟩ := Finset.mem_sdiff.mp hcmem
  obtain ⟨hdV, _⟩ := Finset.mem_sdiff.mp hdmem
  -- the first distinguished request
  set alphaRequest : Request Page := releaseRequest c 1 2 1 zero_lt_one with halphaRequest
  have extendedValid : (empty.appendRequest alphaRequest).Valid :=
    emptyValid.appendRequest alphaRequest (by simp [hempty])
  have hrequests : (empty.appendRequest alphaRequest).requests = [alphaRequest] := by
    simp [hempty, Instance.appendRequest]
  have hmiss : alphaRequest.page ∉
      (algorithm (empty.appendRequest alphaRequest) extendedValid).cacheBefore
        alphaRequest.arrival := by
    rw [online.appendRequest_cacheBefore empty emptyValid alphaRequest extendedValid]
    exact hcmiss
  have hsingle : ∀ {motive : Request Page → Prop},
      motive alphaRequest → ∀ request ∈ (empty.appendRequest alphaRequest).requests,
        motive request := by
    intro motive hmotive request hrequest
    rw [hrequests, List.mem_singleton] at hrequest
    rw [hrequest]
    exact hmotive
  refine ⟨c, d, hcV, hdV, hcd,
    { input := empty.appendRequest alphaRequest
      valid := extendedValid
      size := rfl
      deadline := fun _ => 1 + 2
      chargeWindow := fun _ => 2 + 1
      state := PhaseCount.initial c d
      stateValid := PhaseCount.initial_valid hk hcV hdV hcd
      clock := 2
      checkpoint := 1
      processed := []
      alpha := ⟨c, 1, 1 + 2⟩
      cert := Certificate.initial hcV hdV hcd rfl le_rfl (by norm_num)
      clockPos := by norm_num
      checkpointLe := by norm_num
      alphaLate := by norm_num
      positive := hsingle (by simp [halphaRequest])
      arrivals := hsingle (by simp [halphaRequest])
      shaped := hsingle (by
        rw [halphaRequest]
        exact releaseRequest_shaped c 1 2 1 zero_lt_one)
      pages := hsingle (by simp [halphaRequest, hcV])
      misses := hsingle hmiss
      penalty := hsingle (releaseRequest_penalty c 1 2 1 zero_lt_one)
      free := hsingle (by
        simpa [halphaRequest] using releaseRequest_free c 1 2 1 zero_lt_one)
      ordered := by rw [hrequests]; exact List.pairwise_singleton _ _
      closed := hsingle (Or.inr (by simp [halphaRequest, PhaseCount.initial]))
      alphaClosed := by
        refine hsingle (fun _ => ?_)
        simp only [halphaRequest, releaseRequest_arrival]
        norm_num
      link := hsingle (by simp [halphaRequest])
      steps := 0
      potentialBound := by
        simp [PhaseCount.initial, PhaseCount.Certificate.potential]
      lengthEq := by rw [hrequests]; rfl }, rfl⟩

/-! ## One operation -/

/-- **One operation of the construction.**  The adversary looks at the
algorithm's cache just before the next arrival and releases one request there:
the reserve request on the last cheap candidate when the algorithm has dropped
it — which lets the certificate pay — and otherwise an auxiliary request, which
the certificate processes for free. -/
theorem Run.advance (algorithm : Algorithm Page) (online : algorithm.Online)
    (feasible : algorithm.Feasible) {k : ℕ} (hk : 1 ≤ k) {V start : Finset Page}
    (hcard : V.card = k + 2) (run : Run algorithm k V start) :
    ∃ next : Run algorithm k V start, next.steps = run.steps + 1 := by
  classical
  obtain ⟨a, hta, haD⟩ := exists_between run.alphaLate
  have hcV : run.state.distinguished ∈ V := run.stateValid.distinguished_mem
  have hold : ∀ request ∈ run.input.requests, request.arrival ≠ a := by
    intro request hrequest heq
    exact absurd (heq ▸ run.arrivals request hrequest) (not_le_of_gt hta)
  have hearlier : ∀ request ∈ run.input.requests, request.arrival ≤ a := fun request hrequest =>
    (run.arrivals request hrequest).trans hta.le
  have hapos : 0 < a := run.clockPos.trans hta
  by_cases hpay : ∃ d, run.state.cheap = {d} ∧
      d ∉ (algorithm run.input run.valid).cacheBefore a
  · -- the payment: release the reserve request at `d`, then pay at `alpha.deadline`
    obtain ⟨d, hcheap, hdmiss⟩ := hpay
    have hdcheap : d ∈ run.state.cheap := by rw [hcheap]; simp
    have hdV : d ∈ V := run.stateValid.mem_pages hdcheap
    have hdc : d ≠ run.state.distinguished :=
      Finset.ne_of_mem_erase (run.stateValid.cheap_subset hdcheap)
    set D : Time := run.alpha.deadline with hD
    have haD2 : a ≤ D + 2 := (haD.le.trans (le_self_add))
    set window : Time := (D + 2) - a with hwindow
    have hwindowpos : 0 < window := tsub_pos_of_lt (haD.trans_le le_self_add)
    set beta : Request Page := releaseRequest d a window 1 zero_lt_one with hbeta
    have hbetaDeadline : a + window = D + 2 := add_tsub_cancel_of_le haD2
    have hbetaCharge : a + (window + 1) = D + 2 + 1 := by
      rw [← add_assoc, hbetaDeadline]
    have extendedValid : (run.input.appendRequest beta).Valid :=
      run.valid.appendRequest beta hearlier
    have hmissNew : beta.page ∉
        (algorithm run.input run.valid).cacheBefore beta.arrival := hdmiss
    set deadline' : Request Page → Time :=
      fun request => if request.arrival = a then D + 2 else run.deadline request with hdeadline'
    set chargeWindow' : Request Page → Time :=
      fun request => if request.arrival = a then window + 1 else run.chargeWindow request
      with hchargeWindow'
    have hcw : ∀ request ∈ run.input.requests,
        chargeWindow' request = run.chargeWindow request := by
      intro request hrequest
      simp [hchargeWindow', hold request hrequest]
    have hdl : ∀ request ∈ run.input.requests, deadline' request = run.deadline request := by
      intro request hrequest
      simp [hdeadline', hold request hrequest]
    have hbetaCw : chargeWindow' beta = window + 1 := by simp [hchargeWindow', hbeta]
    have hbetaDl : deadline' beta = D + 2 := by simp [hdeadline', hbeta]
    have hcheapNonempty : (V \ {run.state.distinguished, d}).Nonempty :=
      PhaseCount.refill_nonempty hcard hk hcV hdV (fun heq => hdc heq.symm)
    have hcertArrival : run.checkpoint < beta.arrival := run.checkpointLe.trans_lt hta
    -- the certificate operation, in both flavours
    have hstep : ∃ newState : PhaseCount.Certificate Page,
        PhaseCount.Step V run.state newState ∧ newState.distinguished = d ∧
        Certificate V start (run.alpha :: run.processed) ⟨d, a, D + 2⟩
          newState.distinguished newState.cheap newState.mark newState.budget D := by
      rcases PhaseCount.pay_cases run.stateValid hcheap with hmark | hmark
      · exact ⟨_, PhaseCount.Step.payShort run.state d hcheap hmark, rfl,
          run.cert.pay_short hcheap hmark hcheapNonempty rfl hcertArrival haD le_rfl
            (by norm_num)⟩
      · exact ⟨_, PhaseCount.Step.payLong run.state d hcheap hmark, rfl,
          run.cert.pay_long hcheap hmark hcheapNonempty rfl hcertArrival haD le_rfl
            (by norm_num)⟩
    obtain ⟨newState, hstepping, hdistinguished, hcert⟩ := hstep
    refine ⟨{
      input := run.input.appendRequest beta
      valid := extendedValid
      size := run.size
      deadline := deadline'
      chargeWindow := chargeWindow'
      state := newState
      stateValid := PhaseCount.Step.valid hcard hk run.stateValid hstepping
      clock := D + 1
      checkpoint := D
      processed := run.alpha :: run.processed
      alpha := ⟨d, a, D + 2⟩
      cert := hcert
      clockPos := lt_of_lt_of_le (run.clockPos.trans run.alphaLate) le_self_add
      checkpointLe := le_self_add
      alphaLate := show D + 1 < D + 2 from add_lt_add_of_le_of_lt le_rfl one_lt_two
      positive := ?_
      arrivals := ?_
      shaped := ?_
      pages := ?_
      misses := ?_
      penalty := ?_
      free := ?_
      ordered := ?_
      closed := ?_
      alphaClosed := ?_
      link := ?_
      steps := run.steps + 1
      potentialBound := ?_
      lengthEq := ?_ }, rfl⟩
    · intro request hrequest
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · exact run.positive request hrequest
      · rw [List.mem_singleton.mp hrequest]
        exact hapos
    · intro request hrequest
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · exact ((run.arrivals request hrequest).trans run.alphaLate.le).trans le_self_add
      · rw [List.mem_singleton.mp hrequest]
        exact (haD.le.trans le_self_add)
    · intro request hrequest
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · exact run.shaped request hrequest
      · rw [List.mem_singleton.mp hrequest, hbeta]
        exact releaseRequest_shaped d a window 1 zero_lt_one
    · intro request hrequest
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · exact run.pages request hrequest
      · rw [List.mem_singleton.mp hrequest]
        exact hdV
    · exact appendRequest_misses online run.input run.valid beta extendedValid hearlier
        run.misses hmissNew
    · intro request hrequest
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · rw [hcw request hrequest]
        exact run.penalty request hrequest
      · rw [List.mem_singleton.mp hrequest, hbetaCw]
        exact releaseRequest_penalty d a window 1 zero_lt_one
    · intro request hrequest
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · rw [hdl request hrequest]
        exact run.free request hrequest
      · rw [List.mem_singleton.mp hrequest, hbetaDl]
        have hfree := releaseRequest_free d a window 1 zero_lt_one
        rw [hbetaDeadline] at hfree
        exact hfree
    · refine List.pairwise_append.mpr ⟨?_, List.pairwise_singleton _ _, ?_⟩
      · refine run.ordered.imp_of_mem ?_
        intro first second hfirst _ hcase
        rcases hcase with hpages | hwindows
        · exact Or.inl hpages
        · exact Or.inr (by rw [hcw first hfirst]; exact hwindows)
      · intro first hfirst second hsecond
        rw [List.mem_singleton] at hsecond
        subst hsecond
        rcases run.closed first hfirst with hclosedFirst | hpageFirst
        · refine Or.inr ?_
          rw [hcw first hfirst]
          exact hclosedFirst.trans_lt hta
        · exact Or.inl (by rw [hpageFirst]; exact fun heq => hdc heq.symm)
    · intro request hrequest
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · refine Or.inl ?_
        rw [hcw request hrequest]
        rcases run.closed request hrequest with hclosedRequest | hpageRequest
        · exact hclosedRequest.trans (run.alphaLate.le.trans le_self_add)
        · exact run.alphaClosed request hrequest hpageRequest
      · refine Or.inr ?_
        rw [List.mem_singleton.mp hrequest, hdistinguished]
        rfl
    · intro request hrequest hpage
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · rw [hcw request hrequest]
        rcases run.closed request hrequest with hclosedRequest | hpageRequest
        · exact hclosedRequest.trans ((run.alphaLate.le.trans le_self_add).trans le_self_add)
        · exact (run.alphaClosed request hrequest hpageRequest).trans
            (add_le_add (show D ≤ D + 2 from le_self_add) le_rfl)
      · rw [List.mem_singleton.mp hrequest, hbetaCw]
        exact le_of_eq hbetaCharge
    · intro request hrequest
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · rw [hdl request hrequest]
        exact List.mem_cons_of_mem _ (run.link request hrequest)
      · rw [List.mem_singleton.mp hrequest, hbetaDl]
        exact List.mem_cons_self ..
    · have hstepbound := PhaseCount.Step.potential_le hcard run.stateValid hstepping
      have hprev := run.potentialBound
      omega
    · rw [Instance.appendRequest]
      simp [run.lengthEq]
  · -- an auxiliary request: the algorithm still holds the last cheap candidate
    push_neg at hpay
    obtain ⟨x, hxV, hxc, hxmiss⟩ := exists_uncovered_ne (algorithm run.input run.valid)
      (feasible.scheduleFeasible run.input run.valid) run.size hcard.ge a run.state.distinguished
    have hnonempty : (run.state.cheap.erase x).Nonempty := by
      by_cases hsingleton : ∃ y, run.state.cheap = {y}
      · obtain ⟨y, hy⟩ := hsingleton
        have hycov := hpay y hy
        have hyx : y ≠ x := fun heq => hxmiss (heq ▸ hycov)
        exact ⟨y, Finset.mem_erase.mpr ⟨hyx, by rw [hy]; simp⟩⟩
      · obtain ⟨y, hy⟩ := run.stateValid.nonempty
        have hcard1 : 1 ≤ run.state.cheap.card := Finset.card_pos.mpr ⟨y, hy⟩
        have hcard2 : 2 ≤ run.state.cheap.card := by
          rcases Nat.lt_or_ge run.state.cheap.card 2 with hlt | hge
          · exact absurd (Finset.card_eq_one.mp (by omega)) hsingleton
          · exact hge
        rw [← Finset.card_pos]
        by_cases hxcheap : x ∈ run.state.cheap
        · rw [Finset.card_erase_of_mem hxcheap]; omega
        · rw [Finset.erase_eq_of_notMem hxcheap]; omega
    obtain ⟨w, haw, hwD⟩ := exists_between haD
    obtain ⟨e, hwe, heD⟩ := exists_between hwD
    have hae : a ≤ e := haw.le.trans hwe.le
    set window : Time := w - a with hwindow
    set overshoot : Time := e - w with hovershoot
    have hwindowpos : 0 < window := tsub_pos_of_lt haw
    have hovershootpos : 0 < overshoot := tsub_pos_of_lt hwe
    set gamma : Request Page := releaseRequest x a window overshoot hovershootpos with hgamma
    have hgammaDeadline : a + window = w := add_tsub_cancel_of_le haw.le
    have hgammaCharge : a + (window + overshoot) = e := by
      rw [hwindow, hovershoot, add_comm (w - a) (e - w), tsub_add_tsub_cancel hwe.le haw.le,
        add_tsub_cancel_of_le hae]
    have extendedValid : (run.input.appendRequest gamma).Valid :=
      run.valid.appendRequest gamma hearlier
    set deadline' : Request Page → Time :=
      fun request => if request.arrival = a then w else run.deadline request with hdeadline'
    set chargeWindow' : Request Page → Time :=
      fun request => if request.arrival = a then window + overshoot
        else run.chargeWindow request with hchargeWindow'
    have hcw : ∀ request ∈ run.input.requests,
        chargeWindow' request = run.chargeWindow request := by
      intro request hrequest
      simp [hchargeWindow', hold request hrequest]
    have hdl : ∀ request ∈ run.input.requests, deadline' request = run.deadline request := by
      intro request hrequest
      simp [hdeadline', hold request hrequest]
    have hgammaCw : chargeWindow' gamma = window + overshoot := by simp [hchargeWindow', hgamma]
    have hgammaDl : deadline' gamma = w := by simp [hdeadline', hgamma]
    have hxerase : x ∈ V.erase run.state.distinguished := Finset.mem_erase.mpr ⟨hxc, hxV⟩
    refine ⟨{
      input := run.input.appendRequest gamma
      valid := extendedValid
      size := run.size
      deadline := deadline'
      chargeWindow := chargeWindow'
      state := ⟨run.state.distinguished, run.state.cheap.erase x,
        if run.state.mark = some x then none else run.state.mark, run.state.budget⟩
      stateValid := PhaseCount.Step.valid hcard hk run.stateValid
        (PhaseCount.Step.process run.state x hxc hnonempty)
      clock := e
      checkpoint := e
      processed := ⟨x, a, w⟩ :: run.processed
      alpha := run.alpha
      cert := by
        have := run.cert.process hxerase hnonempty (gamma := ⟨x, a, w⟩) rfl
          (run.checkpointLe.trans_lt hta) hae heD
        exact this
      clockPos := hapos.trans_le hae
      checkpointLe := le_rfl
      alphaLate := heD
      positive := ?_
      arrivals := ?_
      shaped := ?_
      pages := ?_
      misses := ?_
      penalty := ?_
      free := ?_
      ordered := ?_
      closed := ?_
      alphaClosed := ?_
      link := ?_
      steps := run.steps + 1
      potentialBound := ?_
      lengthEq := ?_ }, rfl⟩
    · intro request hrequest
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · exact run.positive request hrequest
      · rw [List.mem_singleton.mp hrequest]
        exact hapos
    · intro request hrequest
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · exact (run.arrivals request hrequest).trans (hta.le.trans hae)
      · rw [List.mem_singleton.mp hrequest]
        exact hae
    · intro request hrequest
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · exact run.shaped request hrequest
      · rw [List.mem_singleton.mp hrequest, hgamma]
        exact releaseRequest_shaped x a window overshoot hovershootpos
    · intro request hrequest
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · exact run.pages request hrequest
      · rw [List.mem_singleton.mp hrequest]
        exact hxV
    · exact appendRequest_misses online run.input run.valid gamma extendedValid hearlier
        run.misses hxmiss
    · intro request hrequest
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · rw [hcw request hrequest]
        exact run.penalty request hrequest
      · rw [List.mem_singleton.mp hrequest, hgammaCw]
        exact releaseRequest_penalty x a window overshoot hovershootpos
    · intro request hrequest
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · rw [hdl request hrequest]
        exact run.free request hrequest
      · rw [List.mem_singleton.mp hrequest, hgammaDl]
        have hfree := releaseRequest_free x a window overshoot hovershootpos
        rw [hgammaDeadline] at hfree
        exact hfree
    · refine List.pairwise_append.mpr ⟨?_, List.pairwise_singleton _ _, ?_⟩
      · refine run.ordered.imp_of_mem ?_
        intro first second hfirst _ hcase
        rcases hcase with hpages | hwindows
        · exact Or.inl hpages
        · exact Or.inr (by rw [hcw first hfirst]; exact hwindows)
      · intro first hfirst second hsecond
        rw [List.mem_singleton] at hsecond
        subst hsecond
        rcases run.closed first hfirst with hclosedFirst | hpageFirst
        · refine Or.inr ?_
          rw [hcw first hfirst]
          exact hclosedFirst.trans_lt hta
        · exact Or.inl (by rw [hpageFirst]; exact fun heq => hxc heq.symm)
    · intro request hrequest
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · rcases run.closed request hrequest with hclosedRequest | hpageRequest
        · exact Or.inl (by rw [hcw request hrequest]; exact hclosedRequest.trans (hta.le.trans hae))
        · exact Or.inr hpageRequest
      · refine Or.inl ?_
        rw [List.mem_singleton.mp hrequest, hgammaCw]
        exact le_of_eq hgammaCharge
    · intro request hrequest hpage
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · rw [hcw request hrequest]
        exact run.alphaClosed request hrequest hpage
      · rw [List.mem_singleton.mp hrequest] at hpage
        exact absurd hpage hxc
    · intro request hrequest
      rcases List.mem_append.mp hrequest with hrequest | hrequest
      · rw [hdl request hrequest]
        rcases List.mem_cons.mp (run.link request hrequest) with hmem | hmem
        · rw [hmem]; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem)
      · rw [List.mem_singleton.mp hrequest, hgammaDl]
        exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · have hstepbound := PhaseCount.Step.potential_le hcard run.stateValid
        (PhaseCount.Step.process run.state x hxc hnonempty)
      have hprev := run.potentialBound
      omega
    · rw [Instance.appendRequest]
      simp [run.lengthEq]

/-! ## Running the construction for as long as we like -/

/-- **The construction runs for any number of operations.** -/
theorem exists_run (algorithm : Algorithm Page) (online : algorithm.Online)
    (feasible : algorithm.Feasible) {k : ℕ} (hk : 1 ≤ k) {V : Finset Page}
    (hcard : V.card = k + 2) (steps : ℕ) :
    ∃ (c d : Page), c ∈ V ∧ d ∈ V ∧ c ≠ d ∧
      ∃ run : Run algorithm k V (V \ {c, d}), run.steps = steps := by
  induction steps with
  | zero => exact exists_initial algorithm online feasible hk hcard
  | succ previous ih =>
      obtain ⟨c, d, hc, hd, hcd, run, hsteps⟩ := ih
      obtain ⟨next, hnext⟩ := Run.advance algorithm online feasible hk hcard run
      exact ⟨c, d, hc, hd, hcd, next, by rw [hnext, hsteps]⟩

end
end PagingWithDelay.DeadlineLowerBound
