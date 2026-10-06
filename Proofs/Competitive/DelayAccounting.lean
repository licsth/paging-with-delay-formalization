import EventLoop
import Mathlib.Algebra.BigOperators.Fin

/-!
# Delay accounting by request position

A request's stable identifier, assigned by `enumerate`, is its position in the
request list.  `requestIdWeight` reads a schedule's delay cost by identifier,
so that sums over sets of identifiers add up to (parts of) the total delay.
-/

namespace PagingWithDelay.Competitive

namespace Schedule

variable {Page : Type*} [DecidableEq Page]

omit [DecidableEq Page] in private theorem mem_enumerateFrom_index
    {requests : List (Request Page)}
    {next : ℕ} {occurrence : Occurrence Page}
    (hmem : occurrence ∈ enumerateFrom next requests) :
    ∃ offset, ∃ hoffset : offset < requests.length,
      occurrence.id = next + offset ∧ requests[offset] = occurrence.request := by
  induction requests generalizing next with
  | nil => simp [enumerateFrom] at hmem
  | cons request rest ih =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact ⟨0, by simp, rfl, rfl⟩
      · obtain ⟨offset, hoffset, hid, hrequest⟩ := ih htail
        exact ⟨offset + 1, by simpa using hoffset, by omega, hrequest⟩

omit [DecidableEq Page] in
/-- Stable identifiers assigned by `enumerate` are precisely the original
request-list positions. -/
theorem mem_enumerate_id_index {requests : List (Request Page)}
    {occurrence : Occurrence Page} (hmem : occurrence ∈ enumerate requests) :
    ∃ hid : occurrence.id < requests.length,
      requests[occurrence.id] = occurrence.request := by
  obtain ⟨offset, hoffset, hid, hrequest⟩ := mem_enumerateFrom_index hmem
  obtain rfl : offset = occurrence.id := by omega
  exact ⟨hoffset, hrequest⟩

omit [DecidableEq Page] in
/-- Convenient bound-only projection of `mem_enumerate_id_index`. -/
theorem id_lt_of_mem_enumerate {requests : List (Request Page)}
    {occurrence : Occurrence Page} (hmem : occurrence ∈ enumerate requests) :
    occurrence.id < requests.length :=
  (mem_enumerate_id_index hmem).choose

/-- Comparator delay weight of a request position.  Values outside the finite
request sequence are zero, allowing class-D batches to be represented solely
by stable natural-number identifiers. -/
noncomputable def requestIdWeight (schedule : PagingWithDelay.Schedule Page)
    (input : Instance Page) (id : ℕ) : Cost :=
  if h : id < input.requests.length then schedule.requestCost input.requests[id]
  else 0

/-- An authentic occurrence's identifier weight is exactly the comparator
cost of that occurrence's request. -/
theorem requestIdWeight_eq_requestCost_of_mem_enumerate
    (schedule : PagingWithDelay.Schedule Page) (input : Instance Page)
    {occurrence : Occurrence Page}
    (hmem : occurrence ∈ enumerate input.requests) :
    requestIdWeight schedule input occurrence.id =
      schedule.requestCost occurrence.request := by
  obtain ⟨hid, hrequest⟩ := mem_enumerate_id_index hmem
  simp only [requestIdWeight, hid, dite_true]
  rw [hrequest]

theorem sum_requestIdWeight_range (schedule : PagingWithDelay.Schedule Page)
    (input : Instance Page) :
    (∑ id ∈ Finset.range input.requests.length,
      requestIdWeight schedule input id) = schedule.totalDelay input := by
  rw [Finset.sum_range]
  simp [requestIdWeight, PagingWithDelay.Schedule.totalDelay]

end Schedule

end PagingWithDelay.Competitive
