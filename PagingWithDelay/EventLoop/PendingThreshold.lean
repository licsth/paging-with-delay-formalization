import PagingWithDelay.EventLoop.Threshold
import PagingWithDelay.EventLoop.RunInvariants

namespace PagingWithDelay.FIFO
variable {Page : Type*} [DecidableEq Page] {δ : Cost}
noncomputable section

theorem pendingCost_continuous (state : State Page) (page : Page) :
    Continuous (pendingCost state page) := by
  unfold pendingCost
  generalize state.pending.filter (fun occurrence => occurrence.request.page = page) = xs
  induction xs with
  | nil => exact continuous_const
  | cons occurrence tail ih =>
    change Continuous (fun t => occurrence.request.delay
      (t - occurrence.request.arrival) +
      (tail.map fun item => item.request.delay (t - item.request.arrival)).sum)
    apply Continuous.add
    · exact occurrence.request.delay_continuous.comp
        (continuous_id.sub continuous_const)
    · exact ih

theorem pendingCost_monotone (state : State Page) (page : Page) :
    Monotone (pendingCost state page) := by
  intro left right hlr
  unfold pendingCost
  generalize state.pending.filter (fun occurrence => occurrence.request.page = page) = xs
  induction xs with
  | nil => exact le_rfl
  | cons occurrence tail ih =>
    change occurrence.request.delay (left - occurrence.request.arrival) +
        (tail.map fun item => item.request.delay (left - item.request.arrival)).sum ≤
      occurrence.request.delay (right - occurrence.request.arrival) +
        (tail.map fun item => item.request.delay (right - item.request.arrival)).sum
    exact add_le_add
      (occurrence.request.delay_mono (tsub_le_tsub_right hlr _)) ih

theorem pendingCost_unbounded_of_pending (state : State Page) (page : Page)
    (hpage : ∃ occurrence ∈ state.pending, occurrence.request.page = page) :
    ∀ bound, ∃ time, bound ≤ pendingCost state page time := by
  intro bound
  obtain ⟨occurrence, hpending, heq⟩ := hpage
  obtain ⟨wait, hwait⟩ := occurrence.request.delay_unbounded bound
  let time := occurrence.request.arrival + wait
  refine ⟨time, hwait.trans ?_⟩
  unfold pendingCost
  apply List.single_le_sum
  · intro cost hcost
    exact bot_le
  · simp only [List.mem_map]
    refine ⟨occurrence, ?_, ?_⟩
    · simp only [List.mem_filter]
      exact ⟨hpending, by simp [heq]⟩
    · simp [time]

theorem thresholdTime_value (state : State Page) (page : Page)
    (hpending : ∃ occurrence ∈ state.pending,
      occurrence.request.page = page)
    (hnow : pendingCost state page state.now ≤ δ) :
    pendingCost state page (thresholdTime δ state page) = δ := by
  exact value_at_sInf_first_crossing_of_unbounded
    (pendingCost state page) state.now δ
    (pendingCost_continuous state page)
    (pendingCost_monotone state page) hnow
    (pendingCost_unbounded_of_pending state page hpending)

/-- A selected payment carries exactly the threshold time of its page. -/
theorem nextPayment_time_eq {state : State Page} {time : Time} {page : Page}
    (hselected : nextPayment? δ state = some (time, page)) :
    thresholdTime δ state page = time := by
  unfold nextPayment? at hselected
  obtain hmem | impossible := foldPayment_mem _ none hselected
  · simp only [List.mem_map] at hmem
    obtain ⟨candidate, _, heq⟩ := hmem
    have hpage : candidate = page := congrArg Prod.snd heq
    subst candidate
    exact congrArg Prod.fst heq
  · simp at impossible

omit [DecidableEq Page] in private theorem earlierPayment_fst_le_left
    (left right : Time × Page) :
    (earlierPayment left right).1 ≤ left.1 := by
  unfold earlierPayment
  split
  · exact le_of_lt (by assumption)
  · exact le_rfl

omit [DecidableEq Page] in private theorem earlierPayment_fst_le_right
    (left right : Time × Page) :
    (earlierPayment left right).1 ≤ right.1 := by
  unfold earlierPayment
  split
  · exact le_rfl
  · exact le_of_not_gt (by assumption)

omit [DecidableEq Page] in private theorem foldPayment_le_each
    (xs : List (Time × Page)) (best : Time × Page) :
    (xs.foldl earlierPayment best).1 ≤ best.1 ∧
      ∀ candidate ∈ xs, (xs.foldl earlierPayment best).1 ≤ candidate.1 := by
  induction xs generalizing best with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons]
    obtain ⟨hleChosen, hleTail⟩ := ih (earlierPayment best head)
    constructor
    · exact hleChosen.trans (earlierPayment_fst_le_left best head)
    · intro candidate hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · exact (hleChosen.trans (earlierPayment_fst_le_right best head)).trans_eq
          (congrArg Prod.fst heq.symm)
      · exact hleTail candidate hmem

/-- The selected payment time is no later than the threshold time of any
currently pending page. -/
theorem nextPayment_time_le_thresholdTime {state : State Page}
    {time : Time} {selected page : Page}
    (hselected : nextPayment? δ state = some (time, selected))
    (hpage : page ∈ pendingPages state) :
    time ≤ thresholdTime δ state page := by
  let candidates := (pendingPages state).map fun page =>
    (thresholdTime δ state page, page)
  have hcandidate0 : (thresholdTime δ state page, page) ∈ candidates := by
    simp [candidates, hpage]
  obtain ⟨head, tail, hcandidates⟩ : ∃ head tail, candidates = head :: tail := by
    cases hc : candidates with
    | nil => simp [hc] at hcandidate0
    | cons head tail => exact ⟨head, tail, rfl⟩
  have optionFold : ∀ (xs : List (Time × Page)) best,
      xs.foldl
        (fun current candidate =>
          some (match current with
            | none => candidate
            | some current => earlierPayment current candidate))
        (some best) = some (xs.foldl earlierPayment best) := by
    intro xs
    induction xs with
    | nil => simp
    | cons candidate tail ih =>
      intro best
      simp only [List.foldl_cons]
      exact ih (earlierPayment best candidate)
  have hfold : tail.foldl earlierPayment head = (time, selected) := by
    unfold nextPayment? at hselected
    rw [show (pendingPages state).map (fun page =>
      (thresholdTime δ state page, page)) = candidates from rfl, hcandidates] at hselected
    simp only [List.foldl_cons] at hselected
    change tail.foldl
      (fun current candidate =>
        some (match current with
          | none => candidate
          | some current => earlierPayment current candidate))
      (some head) = some (time, selected) at hselected
    rw [optionFold tail head] at hselected
    exact Option.some.inj hselected
  have hcandidate : (thresholdTime δ state page, page) ∈ head :: tail := by
    rw [← hcandidates]
    exact hcandidate0
  have hall : ∀ candidate ∈ head :: tail,
      (tail.foldl earlierPayment head).1 ≤ candidate.1 := by
    intro candidate hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with heq | hmem
    · exact (foldPayment_le_each tail head).1.trans_eq
        (congrArg Prod.fst heq.symm)
    · exact (foldPayment_le_each tail head).2 candidate hmem
  have htime := congrArg Prod.fst hfold
  calc
    time = (tail.foldl earlierPayment head).1 := htime.symm
    _ ≤ (thresholdTime δ state page, page).1 := hall _ hcandidate
    _ = thresholdTime δ state page := rfl

theorem selectedPayment_value {state : State Page} {time : Time} {page : Page}
    (hselected : nextPayment? δ state = some (time, page))
    (hnow : pendingCost state page state.now ≤ δ) :
    pendingCost state page time = δ := by
  rw [← nextPayment_time_eq hselected]
  exact thresholdTime_value state page
    (pending_of_mem_pendingPages (nextPayment_mem_pendingPages hselected)) hnow

end
end PagingWithDelay.FIFO
