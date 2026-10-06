import Proofs.Basic.Nonclairvoyant
import Proofs.EventLoop.RunComparison

/-!
# What the event loop reads of a request by time `t`

FIFO inspects a request through its page, its arrival, and its trigger: the
threshold trigger reads the delay curve at the time already waited
(`pendingCost`), the deadline trigger reads its deadline.  This file makes
precise that two states whose pending requests have revealed the same thing by
time `t` select the same payment, or else both select payments strictly after
`t` (`PaymentAgree`):

* `nextPayment?_agree_threshold`: for the threshold trigger, where requests
  reveal their delay so far (`Request.AgreeUpTo`, from `Model.lean`);
* `nextPayment?_agree_deadline`: for the deadline trigger, where requests reveal
  their deadline once it is reached (`Request.DeadlineAgreeUpTo`).

The conclusion is a disjunction because a run may well diverge from its twin
after `t`; all that matters is that it does not do so before.  The relation on
requests is a parameter `R` of the generic part (`OccurrenceRel R`), of which
only page and arrival are used.
-/

namespace PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- Occurrences whose requests are related by `R`.  Their identifiers play no
part: the event loop never reads them. -/
def OccurrenceRel (R : Request Page → Request Page → Prop) (first second : Occurrence Page) :
    Prop :=
  R first.request second.request

/-- Occurrences whose requests have revealed the same delay by time `t`. -/
abbrev OccurrenceAgree (t : Time) : Occurrence Page → Occurrence Page → Prop :=
  OccurrenceRel (Request.AgreeUpTo t)

/-! ## Lists of occurrences -/

section Generic

variable {R : Request Page → Request Page → Prop}
  (hpage : ∀ {first second}, R first second → first.page = second.page)
include hpage

omit [DecidableEq Page] in
theorem map_page_agree {first second : List (Occurrence Page)}
    (agree : List.Forall₂ (OccurrenceRel R) first second) :
    first.map (fun occurrence => occurrence.request.page) =
      second.map (fun occurrence => occurrence.request.page) := by
  induction agree with
  | nil => rfl
  | cons hhead _ ih => simp [hpage hhead, ih]

omit [DecidableEq Page] in
theorem exists_pending_agree {first second : List (Occurrence Page)}
    (agree : List.Forall₂ (OccurrenceRel R) first second) {page : Page}
    (hexists : ∃ occurrence ∈ first, occurrence.request.page = page) :
    ∃ occurrence ∈ second, occurrence.request.page = page :=
  List.mem_map.1 (map_page_agree hpage agree ▸ List.mem_map.2 hexists)

omit [DecidableEq Page] in
theorem filter_agree {first second : List (Occurrence Page)}
    (agree : List.Forall₂ (OccurrenceRel R) first second) (keep : Page → Bool) :
    List.Forall₂ (OccurrenceRel R) (first.filter fun occurrence => keep occurrence.request.page)
      (second.filter fun occurrence => keep occurrence.request.page) := by
  induction agree with
  | nil => simp
  | @cons head other tail others hhead _ ih =>
      simp only [List.filter_cons, hpage hhead]
      split
      · exact .cons hhead ih
      · exact ih

theorem pendingPages_agree {first second : State Page}
    (agree : List.Forall₂ (OccurrenceRel R) first.pending second.pending) :
    pendingPages first = pendingPages second := by
  unfold pendingPages
  rw [map_page_agree hpage agree]

end Generic

omit [DecidableEq Page] in
/-- Every occurrence of the first list has a related counterpart in the second. -/
theorem exists_rel_of_mem {R : Request Page → Request Page → Prop}
    {first second : List (Occurrence Page)}
    (agree : List.Forall₂ (OccurrenceRel R) first second) {occurrence : Occurrence Page}
    (hmem : occurrence ∈ first) :
    ∃ other ∈ second, OccurrenceRel R occurrence other := by
  induction agree with
  | nil => simp at hmem
  | @cons head other tail others hhead _ ih =>
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ⟨other, by simp, hhead⟩
      · obtain ⟨witness, hwitness, hrel⟩ := ih hmem
        exact ⟨witness, List.mem_cons_of_mem _ hwitness, hrel⟩

/-- Two instants each bounding the other once it is at most `t` agree if one of them is. -/
private theorem eq_of_le_of_le {t a b : Time} (hab : a ≤ t → b ≤ a) (hba : b ≤ t → a ≤ b)
    (hle : a ≤ t ∨ b ≤ t) : a = b := by
  rcases hle with h | h
  · exact le_antisymm (hba ((hab h).trans h)) (hab h)
  · exact le_antisymm (hba h) (hab ((hba h).trans h))

/-! ## The threshold trigger -/

section Threshold

variable {δ : Cost}

/-- The pending cost of a page is fixed by what has been revealed: two states
whose pending requests agree up to `t` accrue the same cost at every instant up
to `t`. -/
theorem pendingCost_agree {t : Time} {first second : State Page}
    (agree : List.Forall₂ (OccurrenceAgree t) first.pending second.pending) (page : Page)
    {instant : Time} (hinstant : instant ≤ t) :
    pendingCost first page instant = pendingCost second page instant := by
  have hfilter : List.Forall₂ (OccurrenceAgree t)
      (first.pending.filter fun occurrence => occurrence.request.page = page)
      (second.pending.filter fun occurrence => occurrence.request.page = page) :=
    filter_agree Request.AgreeUpTo.page agree fun candidate => decide (candidate = page)
  unfold pendingCost
  revert hfilter
  generalize first.pending.filter (fun occurrence => occurrence.request.page = page) = xs
  generalize second.pending.filter (fun occurrence => occurrence.request.page = page) = ys
  intro hfilter
  induction hfilter with
  | nil => rfl
  | @cons head other _ _ hhead _ ih =>
      simp only [List.map_cons, List.sum_cons, ih, ← Request.AgreeUpTo.arrival hhead]
      rw [Request.AgreeUpTo.delay hhead _ (tsub_le_tsub_right hinstant _)]

/-! ### Threshold times -/

/-- Any instant at which the threshold has been reached bounds the threshold
time. -/
theorem thresholdTime_le_of_crossing {state : State Page} {page : Page} {instant : Time}
    (hnow : state.now ≤ instant) (hcost : δ ≤ pendingCost state page instant) :
    thresholdTime δ state page ≤ instant :=
  csInf_le ⟨0, fun _ _ => bot_le⟩ ⟨hnow, hcost⟩

private theorem thresholdTime_le_of_le {t : Time} {first second : State Page} {page : Page}
    (hnow : first.now = second.now)
    (agree : List.Forall₂ (OccurrenceAgree t) first.pending second.pending)
    (hbelow : BelowThreshold δ first)
    (hpending : ∃ occurrence ∈ first.pending, occurrence.request.page = page)
    (hle : thresholdTime δ first page ≤ t) :
    thresholdTime δ second page ≤ thresholdTime δ first page := by
  refine thresholdTime_le_of_crossing ?_ ?_
  · rw [← hnow]
    exact thresholdTime_ge_now first page hpending
  · rw [← pendingCost_agree agree page hle]
    exact (thresholdTime_value first page hpending (hbelow page hpending)).ge

/-- Two states that have been told the same story up to `t` schedule a page at
the same time, unless that time lies beyond `t`. -/
theorem thresholdTime_agree {t : Time} {first second : State Page} {page : Page}
    (hnow : first.now = second.now)
    (agree : List.Forall₂ (OccurrenceAgree t) first.pending second.pending)
    (hbelow₁ : BelowThreshold δ first) (hbelow₂ : BelowThreshold δ second)
    (hpending : ∃ occurrence ∈ first.pending, occurrence.request.page = page)
    (hle : thresholdTime δ first page ≤ t ∨ thresholdTime δ second page ≤ t) :
    thresholdTime δ first page = thresholdTime δ second page := by
  have agree' : List.Forall₂ (OccurrenceAgree t) second.pending first.pending :=
    List.Forall₂.flip (agree.imp fun _ _ hagree => Request.AgreeUpTo.symm hagree)
  exact eq_of_le_of_le (thresholdTime_le_of_le hnow agree hbelow₁ hpending)
    (thresholdTime_le_of_le hnow.symm agree' hbelow₂
      (exists_pending_agree Request.AgreeUpTo.page agree hpending)) hle

end Threshold

/-! ## Selecting a payment -/

/-- Two payment candidates a run cannot tell apart before `t`: either the same
candidate, or two that both fall strictly after `t`. -/
def PairAgree (t : Time) (first second : Time × Page) : Prop :=
  first = second ∨ (t < first.1 ∧ t < second.1)

/-- The same, for the optional result of `nextPayment?`. -/
def PaymentAgree (t : Time) (first second : Option (Time × Page)) : Prop :=
  first = second ∨ ∃ left right, first = some left ∧ second = some right ∧
    t < left.1 ∧ t < right.1

omit [DecidableEq Page] in
/-- A payment that is due at or before `t` is the very payment the other state
selects. -/
theorem PaymentAgree.eq_of_le {t time : Time} {page : Page}
    {first second : Option (Time × Page)} (agree : PaymentAgree t first second)
    (hfirst : first = some (time, page)) (hle : time ≤ t) : second = some (time, page) := by
  rcases agree with heq | ⟨left, right, hleft, _, hlate, _⟩
  · rw [← heq]; exact hfirst
  · rw [hfirst] at hleft
    cases hleft
    exact absurd hle (not_le_of_gt hlate)

omit [DecidableEq Page] in
/-- Conversely, if nothing is due at or before `t` on one side, nothing is on
the other. -/
theorem PaymentAgree.late {t : Time} {first second : Option (Time × Page)}
    (agree : PaymentAgree t first second)
    (hfirst : ∀ time page, first = some (time, page) → t < time) :
    ∀ time page, second = some (time, page) → t < time := by
  intro time page hsecond
  rcases agree with heq | ⟨left, right, _, hright, _, hlate⟩
  · exact hfirst time page (heq.trans hsecond)
  · rw [hsecond] at hright
    cases hright
    exact hlate

omit [DecidableEq Page] in
private theorem earlierPayment_agree {t : Time} {best₁ best₂ candidate₁ candidate₂ : Time × Page}
    (hbest : PairAgree t best₁ best₂) (hcandidate : PairAgree t candidate₁ candidate₂) :
    PairAgree t (earlierPayment best₁ candidate₁) (earlierPayment best₂ candidate₂) := by
  unfold earlierPayment PairAgree at *
  rcases hbest with rfl | hbest <;> rcases hcandidate with rfl | hcandidate <;> split_ifs <;>
    first | exact .inl rfl | exact .inr ⟨by order, by order⟩

omit [DecidableEq Page] in
private theorem foldl_earlierPayment_agree {t : Time} {candidates₁ candidates₂ : List (Time × Page)}
    (hcandidates : List.Forall₂ (PairAgree t) candidates₁ candidates₂) :
    ∀ {best₁ best₂ : Time × Page}, PairAgree t best₁ best₂ →
      PairAgree t (candidates₁.foldl earlierPayment best₁)
        (candidates₂.foldl earlierPayment best₂) := by
  induction hcandidates with
  | nil => exact id
  | @cons candidate₁ candidate₂ _ _ hcandidate _ ih =>
      exact fun hbest => ih (earlierPayment_agree hbest hcandidate)

/-- Two states with the same pending pages, whose due times agree before `t`, select
payments that agree before `t`. -/
private theorem nextPayment?_agree {trigger : Trigger} {t : Time} {first second : State Page}
    (hpages : pendingPages first = pendingPages second)
    (hdue : ∀ page ∈ pendingPages first,
      PairAgree t (trigger.dueTime first page, page) (trigger.dueTime second page, page)) :
    PaymentAgree t (nextPayment? trigger first) (nextPayment? trigger second) := by
  rw [nextPayment?_eq, nextPayment?_eq, ← hpages]
  have hall := List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (List.forall₂_same.2 hdue))
  revert hall
  cases pendingPages first with
  | nil => exact fun _ => .inl rfl
  | cons page pages =>
      rintro (_ | ⟨hhead, htail⟩)
      rcases foldl_earlierPayment_agree htail hhead with heq | ⟨h₁, h₂⟩
      · exact .inl (congrArg some heq)
      · exact .inr ⟨_, _, rfl, rfl, h₁, h₂⟩

/-- **What the two runs select agrees before `t`**, for the threshold
trigger.  Two states that have been told the same story up to `t` select the
same payment, unless both selected payments fall after `t`, where the stories
may already differ. -/
theorem nextPayment?_agree_threshold {δ : Cost} {t : Time} {first second : State Page}
    (hnow : first.now = second.now)
    (agree : List.Forall₂ (OccurrenceAgree t) first.pending second.pending)
    (hbelow₁ : BelowThreshold δ first) (hbelow₂ : BelowThreshold δ second) :
    PaymentAgree t (nextPayment? (.threshold δ) first) (nextPayment? (.threshold δ) second) := by
  refine nextPayment?_agree (pendingPages_agree Request.AgreeUpTo.page agree) fun page hpage => ?_
  by_cases hle : thresholdTime δ first page ≤ t ∨ thresholdTime δ second page ≤ t
  · simp [PairAgree, thresholdTime_agree hnow agree hbelow₁ hbelow₂ (mem_pendingPages.1 hpage) hle]
  · push_neg at hle
    exact .inr hle

/-! ## The deadline trigger -/

/-- Occurrences whose requests have revealed the same by time `t` under
deadlines: page, arrival, and the deadline once it is reached. -/
abbrev OccurrenceDeadlineAgree (t : Time) : Occurrence Page → Occurrence Page → Prop :=
  OccurrenceRel (Request.DeadlineAgreeUpTo t)

private theorem deadlineTime_le_of_le {t : Time} {first second : State Page} {page : Page}
    (hnow : first.now = second.now)
    (agree : List.Forall₂ (OccurrenceDeadlineAgree t) first.pending second.pending)
    (hpending : ∃ occurrence ∈ first.pending, occurrence.request.page = page)
    (hle : deadlineTime first page ≤ t) :
    deadlineTime second page ≤ deadlineTime first page := by
  obtain ⟨occurrence, hmem, hpage, hdeadline⟩ :=
    exists_deadline_le_deadlineTime first page hpending
  obtain ⟨other, hother, hrel⟩ := exists_rel_of_mem agree hmem
  have hsame : occurrence.request.deadline = other.request.deadline :=
    hrel.deadline (Or.inl (hdeadline.trans hle))
  refine deadlineTime_le ?_ hother (hrel.page ▸ hpage) (hsame ▸ hdeadline)
  rw [← hnow]
  exact deadlineTime_ge_now first page hpending

/-- Two states that have been told the same story up to `t` under deadlines
schedule a page at the same time, unless that time lies beyond `t`. -/
theorem deadlineTime_agree {t : Time} {first second : State Page} {page : Page}
    (hnow : first.now = second.now)
    (agree : List.Forall₂ (OccurrenceDeadlineAgree t) first.pending second.pending)
    (hpending : ∃ occurrence ∈ first.pending, occurrence.request.page = page)
    (hle : deadlineTime first page ≤ t ∨ deadlineTime second page ≤ t) :
    deadlineTime first page = deadlineTime second page := by
  have agree' : List.Forall₂ (OccurrenceDeadlineAgree t) second.pending first.pending :=
    List.Forall₂.flip (agree.imp fun _ _ hagree =>
      ⟨hagree.page.symm, hagree.arrival.symm, fun h => (hagree.deadline h.symm).symm⟩)
  exact eq_of_le_of_le (deadlineTime_le_of_le hnow agree hpending)
    (deadlineTime_le_of_le hnow.symm agree'
      (exists_pending_agree Request.DeadlineAgreeUpTo.page agree hpending)) hle

/-- **What the two runs select agrees before `t`**, for the deadline trigger. -/
theorem nextPayment?_agree_deadline {t : Time} {first second : State Page}
    (hnow : first.now = second.now)
    (agree : List.Forall₂ (OccurrenceDeadlineAgree t) first.pending second.pending) :
    PaymentAgree t (nextPayment? .deadline first) (nextPayment? .deadline second) := by
  refine nextPayment?_agree (pendingPages_agree Request.DeadlineAgreeUpTo.page agree)
    fun page hpage => ?_
  by_cases hle : deadlineTime first page ≤ t ∨ deadlineTime second page ≤ t
  · simp [PairAgree, deadlineTime_agree hnow agree (mem_pendingPages.1 hpage) hle]
  · push_neg at hle
    exact .inr hle

end
end PagingWithDelay.FIFO
