import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# The paging-with-delay model

Every definition the main theorems mention, and nothing else: requests and instances, schedules and the cost they incur, what makes a schedule feasible, and what makes an algorithm online and nonclairvoyant.

Caches start full.  An instance supplies the common initial cache `C₀` along
with the requests, every schedule — online or offline — starts from it, and no
fetch is charged for the pages it contains.
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

/-- A finite request sequence together with the cache every algorithm starts
from, subject to the conditions under which paging is meaningful: requests
arrive in order, the cache holds at least one page, and the initial cache is
full.  List order breaks ties between arrivals.

`initialCache` is the common full initial cache `C₀` of the write-up, supplied
with the instance at no cost: it lists exactly `cacheSize` distinct pages.  Its
order is the initial FIFO queue, oldest page first; an algorithm or comparator
that does not replace pages first-in-first-out sees only the set
`initialCache.toFinset`. -/
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
Its cardinality is the size of the page universe an instance actually uses,
which is how the results restricted to small universes state their
hypothesis.  It has at least `cacheSize` pages, so
`pageUniverse.card ≤ cacheSize + 1` says the requests touch at most one page
outside the initial cache. -/
def pageUniverse {Page : Type*} [DecidableEq Page] (input : Instance Page) : Finset Page :=
  (input.initialCache ++ input.requests.map Request.page).toFinset

end Instance


/-- One page-fetch event and the cache immediately after it.  Service is not
recorded here: it is derived from the cache trace by `serviceTime`. -/
structure FetchEvent (Page : Type*) [DecidableEq Page] where
  time : Time
  fetched : Page
  cacheAfter : Finset Page

/-- A finite fetch-event trace, starting from the cache `initialCache`.
`Feasible` requires it to be the initial cache of the instance, so the
schedule is a complete cache history whose semantics — service times, delays,
cost — are read off from it alone. -/
structure Schedule (Page : Type*) [DecidableEq Page] where
  initialCache : Finset Page
  events : List (FetchEvent Page)

namespace Schedule

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- Cache contents immediately before time `t`, starting from `initialCache`.
Arrivals at `t` precede all cache transitions stamped `t`. -/
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

/-- The complete feasibility check for an arbitrary, possibly offline, schedule.
All other semantic information is derived from its cache trace.  The schedule
starts from the instance's initial cache: that is the common full initial cache
convention of the write-up, so no fetch is charged for the pages initially
present. -/
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

The definitions below say what it means for an algorithm to be *online* and *nonclairvoyant*.  The former is the usual definition:
what it does up to a time `t` may depend only on the requests that have arrived by `t`.
The latter is more: what it does up to `t` may depend only on the delay those requests have accumulated by `t`, not on the delay curves that produce it.
-/

noncomputable section

variable {Page : Type*}

/-- The requests of `input` that have arrived by time `t`, with the cache size
and initial cache, which are known from the start. -/
def Instance.upTo (input : Instance Page) (t : Time) : Instance Page where
  cacheSize := input.cacheSize
  initialCache := input.initialCache
  requests := input.requests.filter fun request => decide (request.arrival ≤ t)
  chronological := input.chronological.filter _
  positiveCapacity := input.positiveCapacity
  initialCache_nodup := input.initialCache_nodup
  initialCache_full := input.initialCache_full

/-- What a request has revealed by time `t`: the page it asks for, the time it
arrived, and the stretch of its delay curve that has already been traversed. -/
structure Request.AgreeUpTo (t : Time) (first second : Request Page) : Prop where
  page : first.page = second.page
  arrival : first.arrival = second.arrival
  /-- The curves agree at every waiting time that can have elapsed by `t`. -/
  delay : ∀ wait ≤ t - first.arrival, first.delay wait = second.delay wait

/-- Two instances that have revealed the same thing by time `t`: the same cache
size and initial cache, and the requests that have arrived by `t` matched one
for one, each pair agreeing on everything observable at `t`. -/
structure Instance.AgreeUpTo (first second : Instance Page) (t : Time) : Prop where
  cacheSize : first.cacheSize = second.cacheSize
  initialCache : first.initialCache = second.initialCache
  requests : List.Forall₂ (Request.AgreeUpTo t)
    (first.upTo t).requests (second.upTo t).requests

variable [DecidableEq Page]

/-- The events of `schedule` stamped no later than `t`, from the same initial
cache. -/
def Schedule.upTo (schedule : Schedule Page) (t : Time) : Schedule Page :=
  ⟨schedule.initialCache, schedule.events.filter fun event => decide (event.time ≤ t)⟩

/-- A deterministic paging algorithm: it turns every instance into a feasible
schedule. -/
structure Algorithm (Page : Type*) [DecidableEq Page] where
  /-- The schedule the algorithm produces on an instance. -/
  run : Instance Page → Schedule Page
  /-- Every instance receives a feasible schedule. -/
  feasible : ∀ input : Instance Page, (run input).Feasible input

instance : CoeFun (Algorithm Page) fun _ => Instance Page → Schedule Page :=
  ⟨Algorithm.run⟩

/-- An algorithm is **online** when its behaviour up to any time `t` depends
only on the requests that have arrived by `t`.

An algorithm that peeks at a request arriving after `t` violates this; see `Checks/OnlineExamples.lean`. -/
structure Algorithm.Online (algorithm : Algorithm Page) : Prop where
  /-- Instances agreeing up to time `t` receive schedules agreeing up to `t`. -/
  prefixDetermined : ∀ (first second : Instance Page) (t : Time),
    first.upTo t = second.upTo t → (algorithm first).upTo t = (algorithm second).upTo t

/-- An algorithm is **nonclairvoyant** when its behaviour up to any time `t`
depends only on what the input has revealed by `t`: which requests have
arrived, and how much delay each of them has accumulated so far.
`Checks/OnlineExamples.lean` contains provable examples of clairvoyant and nonclairvoyant algorithms by this definition. -/
structure Algorithm.Nonclairvoyant (algorithm : Algorithm Page) : Prop where
  /-- Instances indistinguishable at time `t` receive schedules agreeing up to `t`. -/
  observationDetermined : ∀ (first second : Instance Page) (t : Time),
    first.AgreeUpTo second t → (algorithm first).upTo t = (algorithm second).upTo t

end

end PagingWithDelay
