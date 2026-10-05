import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# The paging-with-delay model

Every definition the main theorems mention: instances, schedules and their cost, feasibility, algorithms, onlineness, nonclairvoyance, deadlines, and competitiveness.

Every schedule starts at no cost from the full initial cache `C₀` supplied by the instance.
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

/-- A finite request sequence in arrival order, with a positive cache size and the full initial cache `C₀` (`cacheSize` distinct pages). List order breaks ties between arrivals.
The order of `initialCache` is FIFO's initial queue, oldest page first. -/
structure Instance (Page : Type*) where
  cacheSize : ℕ
  initialCache : List Page
  requests : List (Request Page)
  /-- Requests occur in nondecreasing order of arrival time. -/
  chronological : requests.Pairwise fun earlier later => earlier.arrival ≤ later.arrival
  positiveCapacity : 0 < cacheSize
  initialCache_nodup : initialCache.Nodup
  initialCache_full : initialCache.length = cacheSize

namespace Instance

/-- The pages the input involves: those initially cached and those requested.
`pageUniverse.card ≤ cacheSize + 1` says the requests touch at most one page outside the initial cache. -/
def pageUniverse {Page : Type*} [DecidableEq Page] (input : Instance Page) : Finset Page :=
  (input.initialCache ++ input.requests.map Request.page).toFinset

end Instance


/-- One page-fetch event and the cache immediately after it. -/
structure FetchEvent (Page : Type*) [DecidableEq Page] where
  time : Time
  fetched : Page
  cacheAfter : Finset Page

/-- A finite fetch-event trace starting from `initialCache`. Service times, delays and cost are derived from it. -/
structure Schedule (Page : Type*) [DecidableEq Page] where
  initialCache : Finset Page
  events : List (FetchEvent Page)

namespace Schedule

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- Cache contents immediately before time `t`. Arrivals at `t` precede all cache transitions stamped `t`. -/
def cacheBefore (schedule : Schedule Page) (t : Time) : Finset Page :=
  schedule.events.foldl
    (fun current event => if event.time < t then event.cacheAfter else current)
    schedule.initialCache

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

/-- Feasibility of an arbitrary, possibly offline, schedule. -/
structure Feasible (schedule : Schedule Page) (input : Instance Page) : Prop where
  initialCache : schedule.initialCache = input.initialCache.toFinset
  chronological : schedule.events.Pairwise fun earlier later =>
    earlier.time ≤ later.time
  validTransitions : ValidTransitionsFrom schedule.initialCache schedule.events
  capacity : ∀ event ∈ schedule.events,
    event.cacheAfter.card ≤ input.cacheSize
  eventuallyServed : ∀ request ∈ input.requests,
    (schedule.serviceCandidates request).Nonempty

end
end Schedule

/-! ## Truncation, online and nonclairvoyant algorithms

An *online* algorithm's behaviour up to time `t` depends only on the requests that have arrived by `t`.
A *nonclairvoyant* one's depends moreover only on the delay those requests have accumulated by `t`.
-/

noncomputable section

variable {Page : Type*}

/-- The requests of `input` that have arrived by time `t`, with the same cache size and initial cache. -/
def Instance.upTo (input : Instance Page) (t : Time) : Instance Page where
  cacheSize := input.cacheSize
  initialCache := input.initialCache
  requests := input.requests.filter fun request => decide (request.arrival ≤ t)
  chronological := input.chronological.filter _
  positiveCapacity := input.positiveCapacity
  initialCache_nodup := input.initialCache_nodup
  initialCache_full := input.initialCache_full

/-- Two requests agree on what they have revealed by time `t`: page, arrival, and delay accrued so far. -/
structure Request.AgreeUpTo (t : Time) (first second : Request Page) : Prop where
  page : first.page = second.page
  arrival : first.arrival = second.arrival
  /-- The curves agree at every waiting time that can have elapsed by `t`. -/
  delay : ∀ wait ≤ t - first.arrival, first.delay wait = second.delay wait

/-- Two instances indistinguishable at time `t`: same cache size and initial cache, and arrived requests matched one for one by `Request.AgreeUpTo`. -/
structure Instance.AgreeUpTo (first second : Instance Page) (t : Time) : Prop where
  cacheSize : first.cacheSize = second.cacheSize
  initialCache : first.initialCache = second.initialCache
  requests : List.Forall₂ (Request.AgreeUpTo t)
    (first.upTo t).requests (second.upTo t).requests

variable [DecidableEq Page]

/-- The events of `schedule` stamped no later than `t`. -/
def Schedule.upTo (schedule : Schedule Page) (t : Time) : Schedule Page :=
  ⟨schedule.initialCache, schedule.events.filter fun event => decide (event.time ≤ t)⟩

/-- A deterministic paging algorithm: it turns every instance into a feasible schedule. -/
structure Algorithm (Page : Type*) [DecidableEq Page] where
  /-- The schedule the algorithm produces on an instance. -/
  run : Instance Page → Schedule Page
  /-- Every instance receives a feasible schedule. -/
  feasible : ∀ input : Instance Page, (run input).Feasible input

/-- Lets an algorithm be applied to an instance like a function: `algorithm input` means `algorithm.run input`. -/
instance : CoeFun (Algorithm Page) fun _ => Instance Page → Schedule Page :=
  ⟨Algorithm.run⟩

/-- An algorithm is **online** when its behaviour up to any time `t` depends only on the requests that have arrived by `t`. See `Checks/OnlineExamples.lean` for examples. -/
structure Algorithm.Online (algorithm : Algorithm Page) : Prop where
  /-- Instances agreeing up to time `t` receive schedules agreeing up to `t`. -/
  prefixDetermined : ∀ (first second : Instance Page) (t : Time),
    first.upTo t = second.upTo t → (algorithm first).upTo t = (algorithm second).upTo t

/-- An algorithm is **nonclairvoyant** when its behaviour up to any time `t` depends only on which requests have arrived by `t` and how much delay each has accumulated. See `Checks/OnlineExamples.lean` for examples. -/
structure Algorithm.Nonclairvoyant (algorithm : Algorithm Page) : Prop where
  /-- Instances indistinguishable at time `t` receive schedules agreeing up to `t`. -/
  observationDetermined : ∀ (first second : Instance Page) (t : Time),
    first.AgreeUpTo second t → (algorithm first).upTo t = (algorithm second).upTo t

/-! ## Deadlines

A request is served by its *deadline* exactly when it incurs no delay cost. Paging with deadlines asks to always do so with the fewest fetches.
A nonclairvoyant deadline algorithm learns a deadline only when it is reached.
-/

/-- The deadline of a request: the last time at which its delay is still zero. -/
def Request.deadline (request : Request Page) : Time :=
  request.arrival + sInf {wait | 0 < request.delay wait}

/-- Two requests agree on what they have revealed by time `t` when paging with deadlines: page, arrival, and the deadline once it has been reached. -/
structure Request.DeadlineAgreeUpTo (t : Time) (first second : Request Page) : Prop where
  page : first.page = second.page
  arrival : first.arrival = second.arrival
  /-- A deadline is revealed when it is reached. -/
  deadline : first.deadline ≤ t ∨ second.deadline ≤ t → first.deadline = second.deadline

/-- Two instances indistinguishable at time `t` when paging with deadlines: same cache size and initial cache, and arrived requests matched one for one by `Request.DeadlineAgreeUpTo`. -/
structure Instance.DeadlineAgreeUpTo (first second : Instance Page) (t : Time) : Prop where
  cacheSize : first.cacheSize = second.cacheSize
  initialCache : first.initialCache = second.initialCache
  requests : List.Forall₂ (Request.DeadlineAgreeUpTo t)
    (first.upTo t).requests (second.upTo t).requests

/-- A deterministic algorithm that meets every deadline on every instance. -/
structure DeadlineAlgorithm (Page : Type*) [DecidableEq Page] extends Algorithm Page where
  /-- Every request is served while its delay is still zero. -/
  meetsDeadlines : ∀ (input : Instance Page), ∀ request ∈ input.requests,
    (run input).requestCost request = 0

/-- The same coercion for deadline algorithms; Lean does not inherit it through `extends`. -/
instance : CoeFun (DeadlineAlgorithm Page) fun _ => Instance Page → Schedule Page :=
  ⟨fun algorithm => algorithm.run⟩

/-- A deadline algorithm is **nonclairvoyant** when its behaviour up to any time `t` depends only on which requests have arrived by `t` and which of their deadlines have been reached by `t`.
`Algorithm.Nonclairvoyant` cannot hold here: a deadline at `t` shows in the delay only after `t`. -/
structure DeadlineAlgorithm.Nonclairvoyant (algorithm : DeadlineAlgorithm Page) : Prop where
  /-- Instances indistinguishable at time `t` receive schedules agreeing up to `t`. -/
  observationDetermined : ∀ (first second : Instance Page) (t : Time),
    first.DeadlineAgreeUpTo second t → (algorithm first).upTo t = (algorithm second).upTo t

/-! ## Competitiveness

An algorithm is compared, instance by instance, with every other algorithm, online or not, i.e. with `OPT`.
Ratio and additive constant may depend on the cache size `k`. The optional predicate `inputs` restricts the instances considered.
-/

/-- `algorithm` is **`ratio`-competitive** on the instances satisfying `inputs`: on cache size `k` it costs at most `ratio k` times any comparator, plus a constant depending on `k`. -/
def Algorithm.Competitive (algorithm : Algorithm Page) (ratio : ℕ → Cost)
    (inputs : Instance Page → Prop := fun _ => True) : Prop :=
  ∃ additive : ℕ → Cost, ∀ (comparator : Algorithm Page) (input : Instance Page),
    inputs input →
      (algorithm input).totalCost input ≤
        ratio input.cacheSize * (comparator input).totalCost input + additive input.cacheSize

/-- `algorithm` is **strictly `ratio`-competitive**: competitive with additive constant `0`. -/
def Algorithm.StrictlyCompetitive (algorithm : Algorithm Page) (ratio : ℕ → Cost)
    (inputs : Instance Page → Prop := fun _ => True) : Prop :=
  ∀ (comparator : Algorithm Page) (input : Instance Page), inputs input →
    (algorithm input).totalCost input ≤ ratio input.cacheSize * (comparator input).totalCost input

/-- Competitiveness for paging with deadlines, against every other deadline algorithm. -/
def DeadlineAlgorithm.Competitive (algorithm : DeadlineAlgorithm Page) (ratio : ℕ → Cost)
    (inputs : Instance Page → Prop := fun _ => True) : Prop :=
  ∃ additive : ℕ → Cost, ∀ (comparator : DeadlineAlgorithm Page) (input : Instance Page),
    inputs input →
      (algorithm input).totalCost input ≤
        ratio input.cacheSize * (comparator input).totalCost input + additive input.cacheSize

/-- Strict competitiveness for paging with deadlines: competitive with additive constant `0`. -/
def DeadlineAlgorithm.StrictlyCompetitive (algorithm : DeadlineAlgorithm Page) (ratio : ℕ → Cost)
    (inputs : Instance Page → Prop := fun _ => True) : Prop :=
  ∀ (comparator : DeadlineAlgorithm Page) (input : Instance Page), inputs input →
    (algorithm input).totalCost input ≤ ratio input.cacheSize * (comparator input).totalCost input

end

end PagingWithDelay
