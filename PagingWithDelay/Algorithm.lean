import PagingWithDelay.Model

/-!
# The FIFO algorithm with threshold `δ`

The definitions of the algorithm the main theorem exhibits.  A page is fetched
once the total delay accumulated by its pending requests reaches the threshold
`δ : Cost`, and the cache is maintained by first-in-first-out replacement.
Every threshold is admissible: `Cost = NNReal`, so `δ` is nonnegative by
construction.  The upper-bound theorem is about `schedule 1`, threshold-one
FIFO; the event loop itself is parametric in `δ`.

Exact threshold crossings of arbitrary continuous curves are not computable, so
the event loop is a `noncomputable` mathematical description rather than
executable code.  The public schedule is obtained by erasing the internal
payment log, so the two histories cannot disagree.
-/

namespace PagingWithDelay

/-- A request occurrence with a stable identifier. -/
structure Occurrence (Page : Type*) where
  id : ℕ
  request : Request Page

def enumerateFrom {Page : Type*} (nextId : ℕ) :
    List (Request Page) → List (Occurrence Page)
  | [] => []
  | request :: rest =>
      { id := nextId, request := request } :: enumerateFrom (nextId + 1) rest

def enumerate {Page : Type*} (requests : List (Request Page)) : List (Occurrence Page) :=
  enumerateFrom 0 requests

namespace FIFO

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- Audit record produced by one threshold payment. The public cache trace is
derived from these records; it is not maintained independently. -/
structure Payment (Page : Type*) [DecidableEq Page] where
  time : Time
  page : Page
  served : List (Occurrence Page)
  queueAfter : List Page

/-- FIFO's internal event-loop state. The front of `queue` is the oldest page.
Requests leave `unseen` on arrival and `pending` on service. -/
structure State (Page : Type*) [DecidableEq Page] where
  now : Time
  queue : List Page
  unseen : List (Occurrence Page)
  pending : List (Occurrence Page)
  payments : List (Payment Page)

def initialState (input : Instance Page) : State Page where
  now := 0
  queue := []
  unseen := enumerate input.requests
  pending := []
  payments := []

/-- Accumulated delay of the pending requests for `page` at `t`. -/
def pendingCost (state : State Page) (page : Page) (t : Time) : Cost :=
  ((state.pending.filter fun occurrence => occurrence.request.page = page).map fun occurrence =>
    occurrence.request.delay (t - occurrence.request.arrival)).sum

/-- First time at or after `now` when a pending page has accumulated the
threshold `δ`.  Attainment and equality at the threshold follow later from the
state invariant, continuity, monotonicity, and unboundedness. -/
def thresholdTime (δ : Cost) (state : State Page) (page : Page) : Time :=
  sInf {t : Time | state.now ≤ t ∧ δ ≤ pendingCost state page t}

/-- Distinct pending pages in first-request order, used for deterministic ties. -/
def pendingPages (state : State Page) : List Page :=
  (state.pending.map fun occurrence => occurrence.request.page).eraseDups

/-- Keep the earlier payment; on equal times keep the left-hand candidate. -/
def earlierPayment (left right : Time × Page) : Time × Page :=
  if right.1 < left.1 then right else left

/-- Earliest currently scheduled threshold payment, if one exists. -/
def nextPayment? (δ : Cost) (state : State Page) : Option (Time × Page) :=
  ((pendingPages state).map fun page => (thresholdTime δ state page, page)).foldl
    (fun best candidate =>
      some (match best with
        | none => candidate
        | some current => earlierPayment current candidate)) none

inductive Action (Page : Type*) where
  | arrival (occurrence : Occurrence Page)
  | payment (time : Time) (page : Page)

/-- Arrivals win ties with payments. The request list resolves arrival ties. -/
def nextAction? (δ : Cost) (state : State Page) : Option (Action Page) :=
  match state.unseen, nextPayment? δ state with
  | [], none => none
  | occurrence :: _, none => some (.arrival occurrence)
  | [], some (time, page) => some (.payment time page)
  | occurrence :: _, some (time, page) =>
      if occurrence.request.arrival ≤ time then some (.arrival occurrence)
      else some (.payment time page)

/-- FIFO replacement. This operation is called only for a page outside the
cache when the event-loop invariant holds. -/
def insertPage (cacheSize : ℕ) (queue : List Page) (page : Page) : List Page :=
  if queue.length < cacheSize then queue ++ [page]
  else queue.tail ++ [page]

/-- Perform one arrival or threshold-payment action. -/
def step (input : Instance Page) (state : State Page) (action : Action Page) : State Page :=
  match action with
  | .arrival occurrence =>
      { state with
        now := occurrence.request.arrival
        unseen := state.unseen.tail
        pending := if occurrence.request.page ∈ state.queue then state.pending
          else state.pending ++ [occurrence] }
  | .payment time page =>
      let queue := insertPage input.cacheSize state.queue page
      let served := state.pending.filter fun occurrence => occurrence.request.page = page
      { state with
        now := time
        queue := queue
        pending := state.pending.filter fun occurrence => occurrence.request.page ≠ page
        payments := state.payments ++ [{ time, page, served, queueAfter := queue }] }

/-- Execute at most `fuel` events. A later invariant proves that twice the
request count suffices: each arrival consumes an unseen request and each
payment consumes at least one pending request. -/
def run (δ : Cost) (input : Instance Page) : ℕ → State Page → State Page
  | 0, state => state
  | fuel + 1, state =>
      match nextAction? δ state with
      | none => state
      | some action => run δ input fuel (step input state action)

/-- The FIFO schedule with threshold `δ` for a finite request sequence. Exact
roots of arbitrary continuous functions make this a mathematical, noncomputable
algorithm rather than executable numerical code.  `schedule 1` is the
threshold-one FIFO of the upper-bound theorem. -/
def schedule (δ : Cost) (input : Instance Page) (_valid : input.Valid) : Schedule Page :=
  let final := run δ input (2 * input.requests.length) (initialState input)
  ⟨final.payments.map fun payment =>
    { time := payment.time
      fetched := payment.page
      cacheAfter := payment.queueAfter.toFinset }⟩

end
end FIFO

end PagingWithDelay
