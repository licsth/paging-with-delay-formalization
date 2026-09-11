import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# The paging-with-delay model

Every definition the main theorems mention, and nothing else: requests and instances, schedules and the cost they incur, what makes a schedule feasible, and what makes an algorithm online and nonclairvoyant.
-/

namespace PagingWithDelay

abbrev Time := NNReal
abbrev Cost := NNReal

/-- A request for a page, with arrival time and delay-cost curve. -/
structure Request (Page : Type*) where
  page : Page
  arrival : Time
  delay : Time → Cost
  delay_continuous : Continuous delay
  delay_mono : Monotone delay
  delay_zero : delay 0 = 0
  delay_unbounded : ∀ bound : Cost, ∃ wait : Time, bound ≤ delay wait

/-- A finite request sequence. List order breaks ties between arrivals. -/
structure Instance (Page : Type*) where
  cacheSize : ℕ
  requests : List (Request Page)

namespace Instance

/-- Requests occur in nondecreasing order of arrival time. -/
def Chronological {Page : Type*} (input : Instance Page) : Prop :=
  input.requests.Pairwise fun earlier later => earlier.arrival ≤ later.arrival

/-- Preconditions under which paging and the FIFO event loop are meaningful. -/
structure Valid {Page : Type*} (input : Instance Page) : Prop where
  chronological : input.Chronological
  positiveCapacity : 0 < input.cacheSize

/-- The pages the input asks for.  Its cardinality is the size of the page
universe an instance actually uses, which is how the results restricted to
small universes state their hypothesis. -/
def pageUniverse {Page : Type*} [DecidableEq Page] (input : Instance Page) : Finset Page :=
  (input.requests.map Request.page).toFinset

end Instance


/-- One page-fetch event and the cache immediately after it.  Service is not
recorded here: it is derived from the cache trace by `serviceTime`. -/
structure FetchEvent (Page : Type*) [DecidableEq Page] where
  time : Time
  fetched : Page
  cacheAfter : Finset Page

/-- A finite fetch-event trace. The cache before its first event is empty. -/
structure Schedule (Page : Type*) [DecidableEq Page] where
  events : List (FetchEvent Page)

namespace Schedule

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- Cache contents immediately before time `t`. Arrivals at `t` precede all cache transitions stamped `t`. -/
def cacheBefore (schedule : Schedule Page) (t : Time) : Finset Page :=
  schedule.events.foldl
    (fun current event => if event.time < t then event.cacheAfter else current) ∅

/-- Every time at which the trace can serve a request. -/
def serviceCandidates (schedule : Schedule Page) (request : Request Page) : Finset Time :=
  let fetchTimes :=
    ((schedule.events.filter fun event =>
      request.arrival ≤ event.time ∧ request.page = event.fetched).map
        FetchEvent.time).toFinset
  if request.page ∈ schedule.cacheBefore request.arrival then
    insert request.arrival fetchTimes
  else
    fetchTimes

/-- Earliest service time, derived from the cache trace. -/
def serviceTime (schedule : Schedule Page) (request : Request Page) : Option Time :=
  if h : (schedule.serviceCandidates request).Nonempty then
    some ((schedule.serviceCandidates request).min' h)
  else
    none

/-- Delay of a request. The default matters only for an infeasible trace. -/
def serviceDelay (schedule : Schedule Page) (request : Request Page) : Time :=
  (schedule.serviceTime request).getD request.arrival - request.arrival

def requestCost (schedule : Schedule Page) (request : Request Page) : Cost :=
  request.delay (schedule.serviceDelay request)

/-- Local consistency of a fetch-event trace, starting from `previous`. -/
def ValidTransitionsFrom (previous : Finset Page) : List (FetchEvent Page) → Prop
  | [] => True
  | event :: rest =>
      event.fetched ∈ event.cacheAfter ∧
      event.cacheAfter \ previous = {event.fetched} ∧
      ValidTransitionsFrom event.cacheAfter rest

def fetchCount (schedule : Schedule Page) : ℕ :=
  schedule.events.length

def totalDelay (schedule : Schedule Page) (input : Instance Page) : Cost :=
  (input.requests.map schedule.requestCost).sum

def totalCost (schedule : Schedule Page) (input : Instance Page) : Cost :=
  schedule.fetchCount + schedule.totalDelay input

/-- The complete feasibility check for an arbitrary, possibly offline, schedule. All other semantic information is derived from its cache trace. -/
structure Feasible (schedule : Schedule Page) (input : Instance Page) : Prop where
  chronological : schedule.events.Pairwise fun earlier later =>
    earlier.time ≤ later.time
  validTransitions : ValidTransitionsFrom ∅ schedule.events /- we use the convention that an algorithm starts from an empty cache -/
  capacity : ∀ event ∈ schedule.events,
    event.cacheAfter.card ≤ input.cacheSize
  eventuallyServed : ∀ request ∈ input.requests,
    (schedule.serviceCandidates request).Nonempty

end
end Schedule

/-! ## Truncation, online and nonclairvoyant algorithms

The definitions below say what it means for an algorithm to be *online* and *nonclairvoyant*.  The former is the usual definition:
what it does up to a time `t` may depend only on the requests that have arrived by `t`.
The latter is more: what it does up to `t` may depend only on the delay those requests have accumulated by `t`, not on the delay curves that produce it.
-/

noncomputable section

variable {Page : Type*}

/-- The requests of `input` that have arrived by time `t`. -/
def Instance.upTo (input : Instance Page) (t : Time) : Instance Page where
  cacheSize := input.cacheSize
  requests := input.requests.filter fun request => decide (request.arrival ≤ t)

/-- What a request has revealed by time `t`: the page it asks for, the time it
arrived, and the stretch of its delay curve that has already been traversed. -/
structure Request.AgreeUpTo (t : Time) (first second : Request Page) : Prop where
  page : first.page = second.page
  arrival : first.arrival = second.arrival
  /-- The curves agree at every waiting time that can have elapsed by `t`. -/
  delay : ∀ wait ≤ t - first.arrival, first.delay wait = second.delay wait

/-- Two instances that have revealed the same thing by time `t`: the same cache
size, and the requests that have arrived by `t` matched one for one, each pair
agreeing on everything observable at `t`. -/
structure Instance.AgreeUpTo (first second : Instance Page) (t : Time) : Prop where
  cacheSize : first.cacheSize = second.cacheSize
  requests : List.Forall₂ (Request.AgreeUpTo t)
    (first.upTo t).requests (second.upTo t).requests

variable [DecidableEq Page]

/-- The events of `schedule` stamped no later than `t`. -/
def Schedule.upTo (schedule : Schedule Page) (t : Time) : Schedule Page :=
  ⟨schedule.events.filter fun event => decide (event.time ≤ t)⟩

/-- A deterministic paging algorithm: it turns a legal instance into a schedule. -/
abbrev Algorithm (Page : Type*) [DecidableEq Page] :=
  ∀ input : Instance Page, input.Valid → Schedule Page

/-- An algorithm is **online** when its behaviour up to any time `t` depends
only on the requests that have arrived by `t`.

An algorithm that peeks at a request arriving after `t` violates this; see `PagingWithDelay/OnlineExamples.lean`. -/
structure Algorithm.Online (algorithm : Algorithm Page) : Prop where
  /-- Instances agreeing up to time `t` receive schedules agreeing up to `t`. -/
  prefixDetermined : ∀ (first second : Instance Page)
    (hfirst : first.Valid) (hsecond : second.Valid) (t : Time),
    first.upTo t = second.upTo t →
    (algorithm first hfirst).upTo t = (algorithm second hsecond).upTo t

/-- An algorithm is **nonclairvoyant** when its behaviour up to any time `t`
depends only on what the input has revealed by `t`: which requests have
arrived, and how much delay each of them has accumulated so far.
`PagingWithDelay/OnlineExamples.lean` contains provable example of clairvoyant and nonclairvoyant algorithms by this definition. -/
structure Algorithm.Nonclairvoyant (algorithm : Algorithm Page) : Prop where
  /-- Instances indistinguishable at time `t` receive schedules agreeing up to `t`. -/
  observationDetermined : ∀ (first second : Instance Page)
    (hfirst : first.Valid) (hsecond : second.Valid) (t : Time),
    first.AgreeUpTo second t →
    (algorithm first hfirst).upTo t = (algorithm second hsecond).upTo t

/-- An algorithm is **feasible** when the schedule it produces is feasible for
every legal instance.  This is `Schedule.Feasible` asked of the algorithm
rather than of one of its runs. -/
structure Algorithm.Feasible (algorithm : Algorithm Page) : Prop where
  /-- Every legal instance receives a feasible schedule. -/
  scheduleFeasible : ∀ (input : Instance Page) (valid : input.Valid),
    (algorithm input valid).Feasible input

end

end PagingWithDelay
