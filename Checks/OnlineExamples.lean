import Proofs.FIFO.Online
import Proofs.FIFO.Nonclairvoyant
import Proofs.FIFO.Deadlines

/-!
# Witnesses for the online- and nonclairvoyant-algorithm definitions

`Model.lean` defines `Algorithm.Online` and `Algorithm.Nonclairvoyant`.  A
definition that everything satisfies, or that nothing satisfies, would carry no
information, so this file pins both predicates down from both sides:

* FIFO is online and nonclairvoyant for every threshold
  (`FIFO.algorithm_online`, `FIFO.algorithm_nonclairvoyant`).  Since an
  `Algorithm` must produce a feasible schedule on every instance, it cannot pass
  merely by ignoring the requests.
* `clairvoyantAlgorithm_not_online` exhibits an algorithm that is rejected.  It
  runs FIFO with threshold `0` when the input contains a second request and
  FIFO with threshold `1` otherwise, so what it does at time `0` depends on a
  request that arrives later — exactly the lookahead the definition must forbid.
* `anticipatingAlgorithm_online` and
  `anticipatingAlgorithm_not_nonclairvoyant` exhibit an algorithm that is
  online but rejected by nonclairvoyance.  It chooses between the same two
  thresholds by reading the delay curve of the first request at a waiting time
  that has not yet elapsed.  It never looks at a request that has not arrived,
  but it does look at delay that has not yet accrued.  So nonclairvoyance is
  strictly stronger than onlineness, and not an elaborate way of restating it.

The witnesses are assembled from FIFO, which is feasible for every threshold.
Two facts about FIFO at time `0` separate the thresholds: with a positive
threshold it never fetches at time `0` (`FIFO.zero_lt_time_of_mem_events`), and
with threshold `0` it serves a growing request arriving at time `0` at once
(`FIFO.exists_event_at_zero`).

None of these witnesses is part of the paper's development; they exist so that
a reader checking the model can see that the two definitions have content.
-/

namespace PagingWithDelay

noncomputable section

/-! ## FIFO at time zero -/

namespace FIFO

variable {Page : Type*} [DecidableEq Page]

/-- With a positive threshold FIFO never fetches at time `0`: every payment
releases `δ` units of delay, and none has accrued at time `0`. -/
theorem zero_lt_time_of_mem_events {δ : Cost} (hδ : 0 < δ) (input : Instance Page)
    {event : FetchEvent Page} (hevent : event ∈ (schedule δ input).events) :
    0 < event.time := by
  rw [schedule_events] at hevent
  obtain ⟨payment, hpayment, rfl⟩ := List.mem_map.mp hevent
  have hcost := final_thresholdPayments (δ := δ) input payment hpayment
  show 0 < payment.time
  rw [pos_iff_ne_zero]
  intro hzero
  have : payment.delayCost = 0 := by
    simp [Payment.delayCost, hzero, Request.delay_zero]
  exact hδ.ne' (hcost.symm.trans this)

/-- With threshold `0` FIFO serves a request arriving at time `0` on a page
outside the initial cache at once, provided its delay grows as soon as it
waits: with threshold `0` it meets every deadline. -/
theorem exists_event_at_zero (input : Instance Page) {request : Request Page}
    (hrequest : request ∈ input.requests) (harrival : request.arrival = 0)
    (hpage : request.page ∉ input.initialCache)
    (hgrows : ∀ wait, request.delay wait = 0 → wait = 0) :
    ∃ event ∈ (schedule 0 input).events, event.time = 0 := by
  have hwait := hgrows _ (schedule_zero_meetsDeadlines input request hrequest)
  have hnonempty := (schedule_feasible 0 input).eventuallyServed request hrequest
  set s := ((schedule 0 input).serviceCandidates request).min' hnonempty with hs
  have hservice : (schedule 0 input).serviceTime request = some s := by
    simp [Schedule.serviceTime, hnonempty, hs]
  have hszero : s = 0 := by
    simpa [Schedule.serviceDelay, hservice, harrival] using hwait
  have hmem : s ∈ (schedule 0 input).serviceCandidates request := Finset.min'_mem _ _
  have hcache : request.page ∉ (schedule 0 input).cacheBefore request.arrival := by
    simpa [Schedule.cacheBefore, harrival, schedule] using hpage
  simp only [Schedule.serviceCandidates, if_neg hcache, List.mem_toFinset,
    List.mem_map, List.mem_filter] at hmem
  obtain ⟨event, ⟨hevent, _⟩, htime⟩ := hmem
  exact ⟨event, hevent, htime.trans hszero⟩

/-- Without requests FIFO does nothing. -/
theorem schedule_events_eq_nil {δ : Cost} {input : Instance Page} (h : input.requests = []) :
    (schedule δ input).events = [] := by
  simp [schedule, h, run, initialState]

end FIFO

/-! ## An algorithm that looks ahead is rejected -/

namespace OnlineCounterexample

/-- A request whose delay grows at rate one, used only to build instances. -/
def request (page : ℕ) (arrival : Time) : Request ℕ where
  page := page
  arrival := arrival
  delay := id
  delay_continuous := continuous_id
  delay_mono := monotone_id
  delay_zero := rfl
  delay_unbounded := fun bound => ⟨bound, le_rfl⟩

/-- One request for page `0` at time `0`, from a cache holding page `2`. -/
def short : Instance ℕ :=
  ⟨1, [2], [request 0 0], by simp, one_pos, by simp, rfl⟩

/-- The same request, plus one arriving later. -/
def long : Instance ℕ :=
  ⟨1, [2], [request 0 0, request 1 1], by simp [request], one_pos, by simp, rfl⟩

/-- The two instances are indistinguishable at time `0`: the second request
has not arrived yet. -/
theorem upTo_zero_eq : short.upTo 0 = long.upTo 0 := by
  simp [Instance.upTo, short, long, request]

/-- FIFO with threshold `0` when it can see that a second request is coming,
FIFO with threshold `1` otherwise.  It is a function of the input, but not of
its past. -/
def clairvoyantAlgorithm : Algorithm ℕ where
  run input :=
    if 2 ≤ input.requests.length then FIFO.schedule 0 input else FIFO.schedule 1 input
  feasible input := by
    split
    · exact FIFO.schedule_feasible 0 input
    · exact FIFO.schedule_feasible 1 input

/-- Looking ahead is exactly what `Algorithm.Online` forbids: on `long` the
algorithm fetches at time `0`, on `short` it does not. -/
theorem clairvoyantAlgorithm_not_online :
    ¬ Algorithm.Online clairvoyantAlgorithm := by
  intro online
  have h := online.prefixDetermined short long 0 upTo_zero_eq
  obtain ⟨event, hevent, htime⟩ := FIFO.exists_event_at_zero long
    (request := request 0 0) (by simp [long]) rfl (by simp [long, request])
    (fun wait hwait => hwait)
  have hlong : event ∈ ((clairvoyantAlgorithm long).upTo 0).events := by
    simp only [Schedule.upTo, List.mem_filter, decide_eq_true_eq]
    exact ⟨by simpa [clairvoyantAlgorithm, long] using hevent, htime.le⟩
  rw [← h] at hlong
  simp only [Schedule.upTo, List.mem_filter, decide_eq_true_eq] at hlong
  have hpos := FIFO.zero_lt_time_of_mem_events one_pos short
    (by simpa [clairvoyantAlgorithm, short] using hlong.1)
  exact absurd hlong.2 (not_le.mpr hpos)

end OnlineCounterexample

/-! ## An algorithm that anticipates delay is rejected

`Algorithm.Online` and `Algorithm.Nonclairvoyant` differ, and the algorithm
below is what separates them.  It runs FIFO with threshold `0` exactly when the
first request will be expensive to keep waiting, a fact it reads off that
request's delay curve.  Before the first request arrives FIFO does nothing
under either threshold, so it never acts on a request that has not arrived: it
is online.  But at the arrival itself no delay has accrued yet, so the number it
consults has not been revealed, and nonclairvoyance rejects it. -/

section Anticipating

variable {Page : Type*} [DecidableEq Page]

/-- Whether the first request would accrue delay `2` after waiting one unit
of time. -/
def Anticipates (input : Instance Page) : Prop :=
  ∃ request ∈ input.requests.head?, 2 ≤ request.delay 1

instance : DecidablePred (Anticipates (Page := Page)) := fun _ => Classical.dec _

/-- FIFO with threshold `0` if the first request anticipates a high delay,
FIFO with threshold `1` otherwise. -/
def anticipatingAlgorithm : Algorithm Page where
  run input :=
    if Anticipates input then FIFO.schedule 0 input else FIFO.schedule 1 input
  feasible input := by
    split
    · exact FIFO.schedule_feasible 0 input
    · exact FIFO.schedule_feasible 1 input

/-- Up to time `t`, the run of either branch is the FIFO run on the input
truncated at `t`. -/
private theorem anticipating_upTo (input : Instance Page) (t : Time) :
    (anticipatingAlgorithm input).upTo t =
      if Anticipates input then (FIFO.schedule 0 (input.upTo t)).upTo t
      else (FIFO.schedule 1 (input.upTo t)).upTo t := by
  unfold anticipatingAlgorithm
  show (if Anticipates input then FIFO.schedule 0 input else FIFO.schedule 1 input).upTo t = _
  split
  · exact FIFO.schedule_upTo_eq input t
  · exact FIFO.schedule_upTo_eq input t

theorem anticipatingAlgorithm_online :
    Algorithm.Online (anticipatingAlgorithm (Page := Page)) where
  prefixDetermined first second t heq := by
    rw [anticipating_upTo first t, anticipating_upTo second t, heq]
    by_cases hempty : (second.upTo t).requests = []
    · -- nothing has arrived: both thresholds leave the truncated input alone
      have hnil (δ : Cost) : (FIFO.schedule δ (second.upTo t)).upTo t =
          ⟨second.initialCache.toFinset, []⟩ := by
        have hevents := FIFO.schedule_events_eq_nil (δ := δ) hempty
        simp only [Schedule.upTo, hevents, List.filter_nil]
        rfl
      split <;> split <;> simp only [hnil]
    · -- the first request has arrived, and both inputs start with it
      have hhead (input : Instance Page) (h : (input.upTo t).requests ≠ []) :
          input.requests.head? = (input.upTo t).requests.head? := by
        cases hreq : input.requests with
        | nil => simp [Instance.upTo, hreq] at h
        | cons r rest =>
            have hr : r.arrival ≤ t := by
              by_contra hlt
              apply h
              have hchrono := input.chronological
              rw [hreq, List.pairwise_cons] at hchrono
              simp only [Instance.upTo, hreq, List.filter_eq_nil_iff, List.mem_cons,
                decide_eq_true_eq]
              rintro x (rfl | hx)
              · exact hlt
              · exact fun hxt => hlt ((hchrono.1 x hx).trans hxt)
            simp [Instance.upTo, hreq, hr]
      have hfirst : (first.upTo t).requests ≠ [] := by rw [heq]; exact hempty
      have hsame : Anticipates first ↔ Anticipates second := by
        unfold Anticipates
        rw [hhead first hfirst, hhead second hempty, heq]
      by_cases hant : Anticipates second
      · simp [hant, hsame.mpr hant]
      · simp [hant, mt hsame.mp hant]

end Anticipating

namespace NonclairvoyanceCounterexample

open OnlineCounterexample (request)

/-- The request of `OnlineCounterexample.request` with its delay doubled.  At
its arrival the two are indistinguishable — neither has accrued anything — and
afterwards they differ. -/
def steepRequest (page : ℕ) (arrival : Time) : Request ℕ where
  page := page
  arrival := arrival
  delay := fun wait => 2 * wait
  delay_continuous := continuous_const.mul continuous_id
  delay_mono := fun first second hle => show 2 * first ≤ 2 * second by gcongr
  delay_zero := by simp
  delay_unbounded := fun bound => ⟨bound, le_mul_of_one_le_left (zero_le _) one_le_two⟩

/-- One request arriving at time `0`, accruing delay at rate one, from a cache
holding page `2`. -/
def gentle : Instance ℕ :=
  ⟨1, [2], [request 0 0], by simp, one_pos, by simp, rfl⟩

/-- The same request arriving at time `0`, accruing delay at rate two. -/
def steep : Instance ℕ :=
  ⟨1, [2], [steepRequest 0 0], by simp, one_pos, by simp, rfl⟩

/-- At time `0` the two instances have revealed the same thing: one request for
page `0`, which has waited no time at all. -/
theorem agreeUpTo_zero : gentle.AgreeUpTo steep 0 where
  cacheSize := rfl
  initialCache := rfl
  requests := by
    have hgentle : (gentle.upTo 0).requests = [request 0 0] := by
      simp [Instance.upTo, gentle, request]
    have hsteep : (steep.upTo 0).requests = [steepRequest 0 0] := by
      simp [Instance.upTo, steep, steepRequest]
    rw [hgentle, hsteep]
    refine List.Forall₂.cons ⟨rfl, rfl, ?_⟩ List.Forall₂.nil
    intro wait hwait
    have hzero : wait = 0 := le_antisymm (by simpa [request] using hwait) (zero_le _)
    simp [request, steepRequest, hzero]

/-- Reading the delay a request has not yet accrued is exactly what
`Algorithm.Nonclairvoyant` forbids, even though `anticipatingAlgorithm_online`
shows that no request beyond the present is ever consulted. -/
theorem anticipatingAlgorithm_not_nonclairvoyant :
    ¬ Algorithm.Nonclairvoyant (anticipatingAlgorithm (Page := ℕ)) := by
  intro nonclairvoyant
  have h := nonclairvoyant.observationDetermined gentle steep 0 agreeUpTo_zero
  have hsteep : Anticipates steep := ⟨steepRequest 0 0, by simp [steep], by
    simp [steepRequest]⟩
  have hgentle : ¬ Anticipates gentle := by
    rintro ⟨r, hr, hdelay⟩
    simp only [gentle, List.head?_cons, Option.mem_def, Option.some.injEq] at hr
    subst hr
    norm_num [request] at hdelay
  obtain ⟨event, hevent, htime⟩ := FIFO.exists_event_at_zero steep
    (request := steepRequest 0 0) (by simp [steep]) rfl (by simp [steep, steepRequest])
    (fun wait hwait => by simpa [steepRequest] using hwait)
  have hmem : event ∈ ((anticipatingAlgorithm steep).upTo 0).events := by
    simp only [Schedule.upTo, List.mem_filter, decide_eq_true_eq]
    refine ⟨?_, htime.le⟩
    show event ∈ (if Anticipates steep then _ else _ : Schedule ℕ).events
    rw [if_pos hsteep]
    exact hevent
  rw [← h] at hmem
  simp only [Schedule.upTo, List.mem_filter, decide_eq_true_eq] at hmem
  have hevent' : event ∈ (FIFO.schedule 1 gentle).events := by
    have := hmem.1
    change event ∈ (if Anticipates gentle then _ else _ : Schedule ℕ).events at this
    rwa [if_neg hgentle] at this
  exact absurd hmem.2 (not_le.mpr (FIFO.zero_lt_time_of_mem_events one_pos gentle hevent'))

end NonclairvoyanceCounterexample

end

end PagingWithDelay
