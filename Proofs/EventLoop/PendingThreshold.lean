import Proofs.EventLoop.Threshold
import Proofs.EventLoop.RunInvariants

namespace PagingWithDelay.FIFO
variable {Page : Type*} [DecidableEq Page] {trigger : Trigger}
noncomputable section

theorem pendingCost_continuous (state : State Page) (page : Page) :
    Continuous (pendingCost state page) :=
  continuous_list_sum _ fun occurrence _ =>
    occurrence.request.delay_continuous.comp (continuous_id.sub continuous_const)

theorem pendingCost_monotone (state : State Page) (page : Page) :
    Monotone (pendingCost state page) := fun _ _ hlr =>
  List.sum_le_sum fun occurrence _ =>
    occurrence.request.delay_mono (tsub_le_tsub_right hlr _)

/-- A pending request for `page` contributes its delay to the pending cost. -/
theorem delay_le_pendingCost {state : State Page} {page : Page} {occurrence : Occurrence Page}
    (hmem : occurrence ∈ state.pending) (hpage : occurrence.request.page = page) (t : Time) :
    occurrence.request.delay (t - occurrence.request.arrival) ≤ pendingCost state page t :=
  List.le_sum_of_mem (List.mem_map_of_mem (List.mem_filter.2 ⟨hmem, by simpa using hpage⟩))

theorem pendingCost_unbounded_of_pending (state : State Page) (page : Page)
    (hpage : ∃ occurrence ∈ state.pending, occurrence.request.page = page) :
    ∀ bound, ∃ time, bound ≤ pendingCost state page time := by
  intro bound
  obtain ⟨occurrence, hpending, heq⟩ := hpage
  obtain ⟨wait, hwait⟩ := occurrence.request.delay_unbounded bound
  refine ⟨occurrence.request.arrival + wait, hwait.trans ?_⟩
  simpa using delay_le_pendingCost hpending heq (occurrence.request.arrival + wait)

theorem thresholdTime_value {δ : Cost} (state : State Page) (page : Page)
    (hpending : ∃ occurrence ∈ state.pending,
      occurrence.request.page = page)
    (hnow : pendingCost state page state.now ≤ δ) :
    pendingCost state page (thresholdTime δ state page) = δ :=
  value_at_sInf_first_crossing_of_unbounded
    (pendingCost state page) state.now δ
    (pendingCost_continuous state page)
    (pendingCost_monotone state page) hnow
    (pendingCost_unbounded_of_pending state page hpending)

theorem thresholdTime_ge_now {δ : Cost} (state : State Page) (page : Page)
    (hpending : ∃ occurrence ∈ state.pending, occurrence.request.page = page) :
    state.now ≤ thresholdTime δ state page := by
  obtain ⟨t, ht⟩ := pendingCost_unbounded_of_pending state page hpending δ
  exact le_csInf ⟨max state.now t, le_max_left _ _,
    ht.trans (pendingCost_monotone state page (le_max_right _ _))⟩ fun _ ht => ht.1

end
end PagingWithDelay.FIFO
