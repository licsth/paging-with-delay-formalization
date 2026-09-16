import PagingWithDelay.Online

/-!
# Witnesses for the online- and nonclairvoyant-algorithm definitions

`Model.lean` defines `Algorithm.Online` and `Algorithm.Nonclairvoyant`.  A
definition that everything satisfies, or that nothing satisfies, would carry no
information, so this file pins both predicates down from both sides:

* `eagerAlgorithm_online` exhibits an online algorithm.  It reacts to the
  requests rather than ignoring them, so it does not pass merely by being a
  constant map.
* `clairvoyantAlgorithm_not_online` exhibits an algorithm that is rejected.  It
  acts at time `0` only when the input happens to contain a second request
  arriving later, which is exactly the lookahead the definition must forbid.
* `anticipatingAlgorithm_online` and
  `anticipatingAlgorithm_not_nonclairvoyant` exhibit an algorithm that is
  online but rejected by nonclairvoyance.  It never looks at a request that has
  not arrived; it looks at the delay a request that *has* arrived is going to
  accrue.  So nonclairvoyance is strictly stronger than onlineness, and not an
  elaborate way of restating it.

None of these witnesses is part of the paper's development; they exist so that
a reader checking the model can see that the two definitions have content.
-/

namespace PagingWithDelay

noncomputable section

variable {Page : Type*} [DecidableEq Page]

/-! ## An online algorithm -/

/-- Fetch every requested page at the moment it is requested, evicting
everything else.  This ignores the future entirely, so it is online; it is
generally *not* feasible, which is why the two notions are kept apart. -/
def eagerAlgorithm : Algorithm Page := fun input _ =>
  ⟨input.initialCache.toFinset, input.requests.map fun request =>
    { time := request.arrival
      fetched := request.page
      cacheAfter := {request.page} }⟩

theorem eagerAlgorithm_online : Algorithm.Online (eagerAlgorithm (Page := Page)) where
  prefixDetermined first second hfirst hsecond t heq := by
    have hrequests :
        first.requests.filter (fun request => decide (request.arrival ≤ t)) =
          second.requests.filter (fun request => decide (request.arrival ≤ t)) := by
      simpa using congrArg Instance.requests heq
    have key : ∀ requests : List (Request Page),
        ((requests.map fun request =>
            ({ time := request.arrival
               fetched := request.page
               cacheAfter := {request.page} } : FetchEvent Page)).filter
          fun event => decide (event.time ≤ t)) =
        (requests.filter fun request => decide (request.arrival ≤ t)).map
          fun request =>
            ({ time := request.arrival
               fetched := request.page
               cacheAfter := {request.page} } : FetchEvent Page) := by
      intro requests
      induction requests with
      | nil => rfl
      | cons request rest ih =>
          by_cases harrival : request.arrival ≤ t <;> simp [harrival, ih]
    have hinitial : first.initialCache = second.initialCache := by
      simpa [Instance.upTo] using congrArg Instance.initialCache heq
    show Schedule.upTo _ t = Schedule.upTo _ t
    simp only [eagerAlgorithm, Schedule.upTo, key, hrequests, hinitial]

end

/-! ## An algorithm that looks ahead is rejected -/

namespace OnlineCounterexample

/-- A request whose delay grows without bound, used only to build instances. -/
noncomputable def request (page : ℕ) (arrival : Time) : Request ℕ where
  page := page
  arrival := arrival
  delay := id
  delay_continuous := continuous_id
  delay_mono := monotone_id
  delay_zero := rfl
  delay_unbounded := fun bound => ⟨bound, le_rfl⟩

/-- One request at time `0`, from a cache holding page `2`. -/
noncomputable def short : Instance ℕ := ⟨1, [2], [request 0 0]⟩

/-- The same request, plus one arriving later. -/
noncomputable def long : Instance ℕ := ⟨1, [2], [request 0 0, request 1 1]⟩

theorem short_valid : short.Valid where
  chronological := by simp [Instance.Chronological, short]
  positiveCapacity := by simp [short]
  initialCache_nodup := by simp [short]
  initialCache_full := by simp [short]

theorem long_valid : long.Valid where
  chronological := by simp [Instance.Chronological, long, request]
  positiveCapacity := by simp [long]
  initialCache_nodup := by simp [long]
  initialCache_full := by simp [long]

/-- The two instances are indistinguishable at time `0`: the second request
has not arrived yet. -/
theorem upTo_zero_eq : short.upTo 0 = long.upTo 0 := by
  simp [Instance.upTo, short, long, request]

/-- An algorithm that acts at time `0` only when it can see that a second
request is coming.  It is a function of the input, but not of its past. -/
noncomputable def clairvoyantAlgorithm : Algorithm ℕ := fun input _ =>
  if 2 ≤ input.requests.length then
    ⟨input.initialCache.toFinset, [{ time := 0, fetched := 0, cacheAfter := {0} }]⟩
  else
    ⟨input.initialCache.toFinset, []⟩

/-- Looking ahead is exactly what `Algorithm.Online` forbids. -/
theorem clairvoyantAlgorithm_not_online :
    ¬ Algorithm.Online clairvoyantAlgorithm := by
  intro online
  have h := online.prefixDetermined short long short_valid long_valid 0 upTo_zero_eq
  simp [clairvoyantAlgorithm, short, long, Schedule.upTo] at h

end OnlineCounterexample

/-! ## An algorithm that anticipates delay is rejected

`Algorithm.Online` and `Algorithm.Nonclairvoyant` differ, and the algorithm
below is what separates them.  It fetches a page exactly when the request for
it will eventually be expensive to keep waiting, a fact it reads off the delay
curve at arrival.  Every event it produces is stamped with the arrival time of
the request that produced it, so it never acts on a request that has not
arrived: it is online.  But at the arrival itself no delay has accrued yet, so
the number it consults has not been revealed, and nonclairvoyance rejects it. -/

noncomputable section

variable {Page : Type*} [DecidableEq Page]

/-- Fetch, on arrival, exactly those pages whose request would accrue delay `2`
after waiting one unit of time. -/
def anticipatingAlgorithm : Algorithm Page := fun input _ =>
  ⟨input.initialCache.toFinset, input.requests.filterMap fun request =>
    if 2 ≤ request.delay 1 then
      some { time := request.arrival, fetched := request.page, cacheAfter := {request.page} }
    else none⟩

theorem anticipatingAlgorithm_online : Algorithm.Online (anticipatingAlgorithm (Page := Page)) where
  prefixDetermined first second hfirst hsecond t heq := by
    have hrequests :
        first.requests.filter (fun request => decide (request.arrival ≤ t)) =
          second.requests.filter (fun request => decide (request.arrival ≤ t)) := by
      simpa using congrArg Instance.requests heq
    have key : ∀ requests : List (Request Page),
        ((requests.filterMap fun request =>
            if 2 ≤ request.delay 1 then
              some ({ time := request.arrival
                      fetched := request.page
                      cacheAfter := {request.page} } : FetchEvent Page)
            else none).filter fun event => decide (event.time ≤ t)) =
        (requests.filter fun request => decide (request.arrival ≤ t)).filterMap fun request =>
          if 2 ≤ request.delay 1 then
            some ({ time := request.arrival
                    fetched := request.page
                    cacheAfter := {request.page} } : FetchEvent Page)
          else none := by
      intro requests
      induction requests with
      | nil => rfl
      | cons request rest ih =>
          by_cases hdelay : 2 ≤ request.delay 1 <;>
            by_cases harrival : request.arrival ≤ t <;> simp [hdelay, harrival, ih]
    have hinitial : first.initialCache = second.initialCache := by
      simpa [Instance.upTo] using congrArg Instance.initialCache heq
    show Schedule.upTo _ t = Schedule.upTo _ t
    simp only [anticipatingAlgorithm, Schedule.upTo, key, hrequests, hinitial]

end

namespace NonclairvoyanceCounterexample

open OnlineCounterexample (request)

/-- The request of `OnlineCounterexample.request` with its delay doubled.  At
its arrival the two are indistinguishable — neither has accrued anything — and
afterwards they differ. -/
noncomputable def steepRequest (page : ℕ) (arrival : Time) : Request ℕ where
  page := page
  arrival := arrival
  delay := fun wait => 2 * wait
  delay_continuous := continuous_const.mul continuous_id
  delay_mono := fun first second hle => show 2 * first ≤ 2 * second by gcongr
  delay_zero := by simp
  delay_unbounded := fun bound => ⟨bound, le_mul_of_one_le_left (zero_le _) one_le_two⟩

/-- One request arriving at time `0`, accruing delay at rate one, from a cache
holding page `2`. -/
noncomputable def gentle : Instance ℕ := ⟨1, [2], [request 0 0]⟩

/-- The same request arriving at time `0`, accruing delay at rate two. -/
noncomputable def steep : Instance ℕ := ⟨1, [2], [steepRequest 0 0]⟩

theorem gentle_valid : gentle.Valid where
  chronological := by simp [Instance.Chronological, gentle]
  positiveCapacity := by simp [gentle]
  initialCache_nodup := by simp [gentle]
  initialCache_full := by simp [gentle]

theorem steep_valid : steep.Valid where
  chronological := by simp [Instance.Chronological, steep]
  positiveCapacity := by simp [steep]
  initialCache_nodup := by simp [steep]
  initialCache_full := by simp [steep]

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
  have hschedules := nonclairvoyant.observationDetermined gentle steep gentle_valid steep_valid 0
    agreeUpTo_zero
  simp [anticipatingAlgorithm, Schedule.upTo, gentle, steep, request, steepRequest]
    at hschedules

end NonclairvoyanceCounterexample

end PagingWithDelay
