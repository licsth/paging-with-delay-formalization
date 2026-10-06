import EventLoop

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page]

noncomputable section

omit [DecidableEq Page] in theorem enumerateFrom_map_request
    (nextId : ℕ) (requests : List (Request Page)) :
    (enumerateFrom nextId requests).map Occurrence.request = requests := by
  induction requests generalizing nextId with
  | nil => rfl
  | cons request rest ih => simp [enumerateFrom, ih]

omit [DecidableEq Page] in theorem enumerate_map_request (requests : List (Request Page)) :
    (enumerate requests).map Occurrence.request = requests :=
  enumerateFrom_map_request 0 requests

omit [DecidableEq Page] in
theorem mem_enumerateFrom_request {start : ℕ} {requests : List (Request Page)}
    {occurrence : Occurrence Page} (hmem : occurrence ∈ enumerateFrom start requests) :
    occurrence.request ∈ requests :=
  enumerateFrom_map_request start requests ▸ List.mem_map_of_mem hmem

/-- Delay charged to the occurrences recorded as served by a payment. -/
def Payment.delayCost (payment : Payment Page) : Cost :=
  (payment.served.map fun occurrence =>
    occurrence.request.delay (payment.time - occurrence.request.arrival)).sum

/-- The audit record made by `step` retains exactly the summands occurring in
`pendingCost` immediately before the payment. -/
theorem payment_delayCost_mk_eq_pendingCost
    (state : State Page) (time : Time) (page : Page) (queueAfter : List Page) :
    Payment.delayCost
        { time := time
          page := page
          served := state.pending.filter fun occurrence =>
            occurrence.request.page = page
          queueAfter := queueAfter } =
      pendingCost state page time := by
  rfl

end
end PagingWithDelay.FIFO
