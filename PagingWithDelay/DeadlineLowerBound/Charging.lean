import PagingWithDelay.Model

/-!
# Deadline-shaped delay curves in this model

`Model.lean` requires every delay curve to be continuous, monotone, zero at
zero and *unbounded*, so a hard deadline — zero delay inside a window and an
infinite penalty outside it — is not a request of this model.  The deadline
drafts therefore have to be reread with a finite penalty: a curve that stays at
zero throughout the window and has risen to some value `penalty` shortly after
it.  This file checks the one property such a curve has to have for the
drafts' charging argument to survive the translation.

`fetch_in_window_or_cost` is the dichotomy: a request whose page is absent when
it arrives is served *only* by a fetch of that page at or after its arrival, so
either that fetch happens inside the window, or the request pays at least what
its curve has accrued by the end of the window.  Charging the first alternative
to the fetch and the second to the request's own delay gives one unit of
`totalCost` per request either way, which is what the drafts' charging lemma
needs — provided the curve has reached `1` by the end of the window that the
adversary uses for charging.  A penalty of `2`, as suggested for "serve it and
come back", is comfortably enough; the argument only needs `1`.

Note the two-sided nature of the statement: the window used here has to be
*strictly longer* than the interval on which the curve is still zero.  A
continuous curve is arbitrarily cheap immediately after its deadline, so
"missed the deadline" alone buys the adversary nothing; "missed the deadline by
`ε`, where the curve has already risen" is what buys a unit.
-/

namespace PagingWithDelay

variable {Page : Type*} [DecidableEq Page]

noncomputable section

namespace Schedule

/-- A request whose page is absent at its arrival can only be served by a fetch
of that page at or after the arrival. -/
theorem exists_fetch_of_miss (schedule : Schedule Page) (request : Request Page)
    (hserved : (schedule.serviceCandidates request).Nonempty)
    (hmiss : request.page ∉ schedule.cacheBefore request.arrival) :
    ∃ event ∈ schedule.events, event.fetched = request.page ∧
      request.arrival ≤ event.time ∧
      schedule.serviceTime request = some event.time := by
  set time := (schedule.serviceCandidates request).min' hserved with htime
  have hmem : time ∈ schedule.serviceCandidates request :=
    Finset.min'_mem _ hserved
  rw [serviceCandidates, if_neg hmiss] at hmem
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hmem
  obtain ⟨event, ⟨hevent, harrival, hpage⟩, heq⟩ := hmem
  exact ⟨event, hevent, hpage.symm, harrival, by rw [serviceTime, dif_pos hserved, heq]⟩

/-- **The charging dichotomy.**  Either the page is fetched within `window` of
the arrival, or the request pays at least the delay its curve has accrued by
the end of the window. -/
theorem fetch_in_window_or_cost (schedule : Schedule Page) (request : Request Page)
    (hserved : (schedule.serviceCandidates request).Nonempty)
    (hmiss : request.page ∉ schedule.cacheBefore request.arrival) (window : Time) :
    (∃ event ∈ schedule.events, event.fetched = request.page ∧
        request.arrival ≤ event.time ∧ event.time ≤ request.arrival + window) ∨
      request.delay window ≤ schedule.requestCost request := by
  obtain ⟨event, hevent, hpage, harrival, hservice⟩ :=
    schedule.exists_fetch_of_miss request hserved hmiss
  by_cases hwindow : event.time ≤ request.arrival + window
  · exact Or.inl ⟨event, hevent, hpage, harrival, hwindow⟩
  · refine Or.inr ?_
    have hlate : window < event.time - request.arrival := by
      rw [lt_tsub_iff_left]
      exact lt_of_not_ge hwindow
    have hdelay : schedule.serviceDelay request = event.time - request.arrival := by
      rw [serviceDelay, hservice]
      rfl
    rw [requestCost, hdelay]
    exact request.delay_mono hlate.le

/-- The form the drafts use: with a curve that has reached `1` by the end of the
window, every request whose page is absent on arrival costs the schedule at
least one unit — either a fetch inside the window, or delay. -/
theorem fetch_in_window_or_unit_cost (schedule : Schedule Page) (request : Request Page)
    (hserved : (schedule.serviceCandidates request).Nonempty)
    (hmiss : request.page ∉ schedule.cacheBefore request.arrival) {window : Time}
    (hpenalty : 1 ≤ request.delay window) :
    (∃ event ∈ schedule.events, event.fetched = request.page ∧
        request.arrival ≤ event.time ∧ event.time ≤ request.arrival + window) ∨
      1 ≤ schedule.requestCost request :=
  (schedule.fetch_in_window_or_cost request hserved hmiss window).imp id
    fun hcost => hpenalty.trans hcost

end Schedule

end
end PagingWithDelay
