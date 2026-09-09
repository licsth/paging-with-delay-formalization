import PagingWithDelay.Online

/-!
# Witnesses for the online-algorithm definition

`PagingWithDelay/Online.lean` defines `Algorithm.Online`.  A definition that
everything satisfies, or that nothing satisfies, would carry no information, so
this file pins the predicate down from both sides:

* `eagerAlgorithm_online` exhibits an online algorithm.  It reacts to the
  requests rather than ignoring them, so it does not pass merely by being a
  constant map.
* `clairvoyantAlgorithm_not_online` exhibits an algorithm that is rejected.  It
  acts at time `0` only when the input happens to contain a second request
  arriving later, which is exactly the lookahead the definition must forbid.

Neither witness is part of the paper's development; they exist so that a reader
checking the model can see that `Algorithm.Online` has content.
-/

namespace PagingWithDelay

noncomputable section

variable {Page : Type*} [DecidableEq Page]

/-! ## An online algorithm -/

/-- Fetch every requested page at the moment it is requested, evicting
everything else.  This ignores the future entirely, so it is online; it is
generally *not* feasible, which is why the two notions are kept apart. -/
def eagerAlgorithm : Algorithm Page := fun input _ =>
  ⟨input.requests.map fun request =>
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
    show Schedule.upTo _ t = Schedule.upTo _ t
    simp only [eagerAlgorithm, Schedule.upTo, key, hrequests]

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

/-- One request at time `0`. -/
noncomputable def short : Instance ℕ := ⟨1, [request 0 0]⟩

/-- The same request, plus one arriving later. -/
noncomputable def long : Instance ℕ := ⟨1, [request 0 0, request 1 1]⟩

theorem short_valid : short.Valid where
  chronological := by simp [Instance.Chronological, short]
  positiveCapacity := by simp [short]

theorem long_valid : long.Valid where
  chronological := by simp [Instance.Chronological, long, request]
  positiveCapacity := by simp [long]

/-- The two instances are indistinguishable at time `0`: the second request
has not arrived yet. -/
theorem upTo_zero_eq : short.upTo 0 = long.upTo 0 := by
  simp [Instance.upTo, short, long, request]

/-- An algorithm that acts at time `0` only when it can see that a second
request is coming.  It is a function of the input, but not of its past. -/
noncomputable def clairvoyantAlgorithm : Algorithm ℕ := fun input _ =>
  if 2 ≤ input.requests.length then
    ⟨[{ time := 0, fetched := 0, cacheAfter := {0} }]⟩
  else
    ⟨[]⟩

/-- Looking ahead is exactly what `Algorithm.Online` forbids. -/
theorem clairvoyantAlgorithm_not_online :
    ¬ Algorithm.Online clairvoyantAlgorithm := by
  intro online
  have h := online.prefixDetermined short long short_valid long_valid 0 upTo_zero_eq
  simp [clairvoyantAlgorithm, short, long, Schedule.upTo] at h

end OnlineCounterexample

end PagingWithDelay
