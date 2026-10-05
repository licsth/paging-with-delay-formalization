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
    ∃ occurrence ∈ second, occurrence.request.page = page := by
  induction agree with
  | nil => simp at hexists
  | @cons head other tail others hhead _ ih =>
      obtain ⟨occurrence, hmem, hpage'⟩ := hexists
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ⟨other, by simp, by rw [← hpage hhead]; exact hpage'⟩
      · obtain ⟨witness, hwitness, hwitness_page⟩ := ih ⟨occurrence, hmem, hpage'⟩
        exact ⟨witness, List.mem_cons_of_mem _ hwitness, hwitness_page⟩

omit [DecidableEq Page] in
theorem filter_agree {first second : List (Occurrence Page)}
    (agree : List.Forall₂ (OccurrenceRel R) first second) (keep : Page → Bool) :
    List.Forall₂ (OccurrenceRel R) (first.filter fun occurrence => keep occurrence.request.page)
      (second.filter fun occurrence => keep occurrence.request.page) := by
  induction agree with
  | nil => simp
  | @cons head other tail others hhead _ ih =>
      have hkeep' : keep head.request.page = keep other.request.page := by
        rw [hpage hhead]
      rw [List.filter_cons, List.filter_cons, ← hkeep']
      by_cases hkeep : keep head.request.page
      · rw [if_pos hkeep, if_pos hkeep]
        exact List.Forall₂.cons hhead ih
      · rw [if_neg hkeep, if_neg hkeep]
        exact ih

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

/-! ## The threshold trigger -/

section Threshold

variable {δ : Cost}

private theorem sum_delay_agree {t : Time} {first second : List (Occurrence Page)}
    (agree : List.Forall₂ (OccurrenceAgree t) first second) (page : Page)
    {instant : Time} (hinstant : instant ≤ t) :
    ((first.filter fun occurrence => occurrence.request.page = page).map fun occurrence =>
        occurrence.request.delay (instant - occurrence.request.arrival)).sum =
      ((second.filter fun occurrence => occurrence.request.page = page).map fun occurrence =>
        occurrence.request.delay (instant - occurrence.request.arrival)).sum := by
  induction agree with
  | nil => rfl
  | @cons head other tail others hhead _ ih =>
      have hpage : decide (head.request.page = page) = decide (other.request.page = page) := by
        rw [Request.AgreeUpTo.page hhead]
      rw [List.filter_cons, List.filter_cons, ← hpage]
      by_cases hkeep : head.request.page = page
      · have hdelay : head.request.delay (instant - head.request.arrival) =
            other.request.delay (instant - other.request.arrival) := by
          rw [← Request.AgreeUpTo.arrival hhead]
          exact Request.AgreeUpTo.delay hhead _ (tsub_le_tsub_right hinstant _)
        rw [if_pos (by simpa using hkeep), if_pos (by simpa using hkeep)]
        simp only [List.map_cons, List.sum_cons, hdelay, ih]
      · rw [if_neg (by simpa using hkeep), if_neg (by simpa using hkeep)]
        exact ih

/-- The pending cost of a page is fixed by what has been revealed: two states
whose pending requests agree up to `t` accrue the same cost at every instant up
to `t`. -/
theorem pendingCost_agree {t : Time} {first second : State Page}
    (agree : List.Forall₂ (OccurrenceAgree t) first.pending second.pending) (page : Page)
    {instant : Time} (hinstant : instant ≤ t) :
    pendingCost first page instant = pendingCost second page instant :=
  sum_delay_agree agree page hinstant

/-! ### Threshold times -/

/-- At the threshold time the cost has indeed reached the threshold. -/
theorem thresholdTime_crossing {state : State Page} {page : Page}
    (hpending : ∃ occurrence ∈ state.pending, occurrence.request.page = page)
    (hbelow : pendingCost state page state.now ≤ δ) :
    δ ≤ pendingCost state page (thresholdTime δ state page) :=
  (thresholdTime_value state page hpending hbelow).ge

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
    exact thresholdTime_crossing hpending (hbelow page hpending)

/-- Two states that have been told the same story up to `t` schedule a page at
the same time, unless that time lies beyond `t`. -/
theorem thresholdTime_agree {t : Time} {first second : State Page} {page : Page}
    (hnow : first.now = second.now)
    (agree : List.Forall₂ (OccurrenceAgree t) first.pending second.pending)
    (hbelow₁ : BelowThreshold δ first) (hbelow₂ : BelowThreshold δ second)
    (hpending : ∃ occurrence ∈ first.pending, occurrence.request.page = page)
    (hle : thresholdTime δ first page ≤ t ∨ thresholdTime δ second page ≤ t) :
    thresholdTime δ first page = thresholdTime δ second page := by
  have agree' : List.Forall₂ (OccurrenceAgree t) second.pending first.pending := by
    apply List.Forall₂.flip
    exact agree.imp fun _ _ hagree => Request.AgreeUpTo.symm hagree
  have hpending' : ∃ occurrence ∈ second.pending, occurrence.request.page = page :=
    exists_pending_agree Request.AgreeUpTo.page agree hpending
  rcases hle with hfirst | hsecond
  · have hsecond : thresholdTime δ second page ≤ t :=
      (thresholdTime_le_of_le hnow agree hbelow₁ hpending hfirst).trans hfirst
    exact le_antisymm
      (thresholdTime_le_of_le hnow.symm agree' hbelow₂ hpending' hsecond)
      (thresholdTime_le_of_le hnow agree hbelow₁ hpending hfirst)
  · have hfirst : thresholdTime δ first page ≤ t :=
      (thresholdTime_le_of_le hnow.symm agree' hbelow₂ hpending' hsecond).trans hsecond
    exact le_antisymm
      (thresholdTime_le_of_le hnow.symm agree' hbelow₂ hpending' hsecond)
      (thresholdTime_le_of_le hnow agree hbelow₁ hpending hfirst)

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
  unfold earlierPayment PairAgree
  rcases hbest with rfl | ⟨hbest₁, hbest₂⟩
  · rcases hcandidate with rfl | ⟨hcandidate₁, hcandidate₂⟩
    · exact Or.inl rfl
    · split
      · rename_i hlt₁
        split
        · exact Or.inr ⟨hcandidate₁, hcandidate₂⟩
        · exact Or.inr ⟨hcandidate₁, hcandidate₁.trans hlt₁⟩
      · rename_i hnlt₁
        split
        · rename_i hlt₂
          exact Or.inr ⟨hcandidate₂.trans hlt₂, hcandidate₂⟩
        · exact Or.inl rfl
  · rcases hcandidate with rfl | ⟨hcandidate₁, hcandidate₂⟩
    · split
      · rename_i hlt₁
        split
        · exact Or.inl rfl
        · rename_i hnlt₂
          exact Or.inr ⟨hbest₂.trans_le (le_of_not_gt hnlt₂), hbest₂⟩
      · rename_i hnlt₁
        split
        · rename_i hlt₂
          exact Or.inr ⟨hbest₁, hbest₁.trans_le (le_of_not_gt hnlt₁)⟩
        · exact Or.inr ⟨hbest₁, hbest₂⟩
    · split <;> split
      · exact Or.inr ⟨hcandidate₁, hcandidate₂⟩
      · exact Or.inr ⟨hcandidate₁, hbest₂⟩
      · exact Or.inr ⟨hbest₁, hcandidate₂⟩
      · exact Or.inr ⟨hbest₁, hbest₂⟩

omit [DecidableEq Page] in
private theorem foldPayment_agree (t : Time) :
    ∀ {candidates₁ candidates₂ : List (Time × Page)},
      List.Forall₂ (PairAgree t) candidates₁ candidates₂ →
      ∀ {best₁ best₂ : Option (Time × Page)}, PaymentAgree t best₁ best₂ →
        PaymentAgree t
          (candidates₁.foldl (fun best candidate =>
            some (match best with
              | none => candidate
              | some current => earlierPayment current candidate)) best₁)
          (candidates₂.foldl (fun best candidate =>
            some (match best with
              | none => candidate
              | some current => earlierPayment current candidate)) best₂) := by
  intro candidates₁ candidates₂ hcandidates
  induction hcandidates with
  | nil =>
      intro best₁ best₂ hbest
      exact hbest
  | @cons candidate₁ candidate₂ rest₁ rest₂ hcandidate _ ih =>
      intro best₁ best₂ hbest
      simp only [List.foldl_cons]
      apply ih
      rcases hbest with rfl | ⟨left, right, hleft, hright, hlate₁, hlate₂⟩
      · cases best₁ with
        | none =>
            rcases hcandidate with rfl | ⟨hlate₁, hlate₂⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨candidate₁, candidate₂, rfl, rfl, hlate₁, hlate₂⟩
        | some current =>
            rcases earlierPayment_agree (t := t) (Or.inl rfl) hcandidate with heq | ⟨h₁, h₂⟩
            · exact Or.inl (congrArg some heq)
            · exact Or.inr ⟨_, _, rfl, rfl, h₁, h₂⟩
      · subst hleft
        subst hright
        rcases earlierPayment_agree (Or.inr ⟨hlate₁, hlate₂⟩) hcandidate with heq | ⟨h₁, h₂⟩
        · exact Or.inl (congrArg some heq)
        · exact Or.inr ⟨_, _, rfl, rfl, h₁, h₂⟩

omit [DecidableEq Page] in
private theorem forall₂_map_of_forall {t : Time} (first second : Page → Time × Page) :
    ∀ (pages : List Page), (∀ page ∈ pages, PairAgree t (first page) (second page)) →
      List.Forall₂ (PairAgree t) (pages.map first) (pages.map second) := by
  intro pages
  induction pages with
  | nil => intro _; simp
  | cons page rest ih =>
      intro hpages
      exact List.Forall₂.cons (hpages page (by simp))
        (ih fun other hother => hpages other (List.mem_cons_of_mem _ hother))

/-- **What the two runs select agrees before `t`**, for the threshold
trigger.  Two states that have been told the same story up to `t` select the
same payment, unless both selected payments fall after `t`, where the stories
may already differ. -/
theorem nextPayment?_agree_threshold {δ : Cost} {t : Time} {first second : State Page}
    (hnow : first.now = second.now)
    (agree : List.Forall₂ (OccurrenceAgree t) first.pending second.pending)
    (hbelow₁ : BelowThreshold δ first) (hbelow₂ : BelowThreshold δ second) :
    PaymentAgree t (nextPayment? (.threshold δ) first) (nextPayment? (.threshold δ) second) := by
  have hpages : pendingPages first = pendingPages second :=
    pendingPages_agree Request.AgreeUpTo.page agree
  unfold nextPayment?
  rw [hpages]
  refine foldPayment_agree t (forall₂_map_of_forall _ _ _ ?_) (Or.inl rfl)
  intro page hpage
  have hpending : ∃ occurrence ∈ first.pending, occurrence.request.page = page :=
    pending_of_mem_pendingPages (hpages ▸ hpage)
  by_cases hle : thresholdTime δ first page ≤ t ∨ thresholdTime δ second page ≤ t
  · exact Or.inl (by
      simp only [Trigger.dueTime]
      rw [thresholdTime_agree hnow agree hbelow₁ hbelow₂ hpending hle])
  · push_neg at hle
    exact Or.inr ⟨hle.1, hle.2⟩

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
  have agree' : List.Forall₂ (OccurrenceDeadlineAgree t) second.pending first.pending := by
    apply List.Forall₂.flip
    exact agree.imp fun _ _ hagree =>
      ⟨hagree.page.symm, hagree.arrival.symm, fun h => (hagree.deadline h.symm).symm⟩
  have hpending' : ∃ occurrence ∈ second.pending, occurrence.request.page = page :=
    exists_pending_agree Request.DeadlineAgreeUpTo.page agree hpending
  rcases hle with hfirst | hsecond
  · have hsecond : deadlineTime second page ≤ t :=
      (deadlineTime_le_of_le hnow agree hpending hfirst).trans hfirst
    exact le_antisymm
      (deadlineTime_le_of_le hnow.symm agree' hpending' hsecond)
      (deadlineTime_le_of_le hnow agree hpending hfirst)
  · have hfirst : deadlineTime first page ≤ t :=
      (deadlineTime_le_of_le hnow.symm agree' hpending' hsecond).trans hsecond
    exact le_antisymm
      (deadlineTime_le_of_le hnow.symm agree' hpending' hsecond)
      (deadlineTime_le_of_le hnow agree hpending hfirst)

/-- **What the two runs select agrees before `t`**, for the deadline trigger. -/
theorem nextPayment?_agree_deadline {t : Time} {first second : State Page}
    (hnow : first.now = second.now)
    (agree : List.Forall₂ (OccurrenceDeadlineAgree t) first.pending second.pending) :
    PaymentAgree t (nextPayment? .deadline first) (nextPayment? .deadline second) := by
  have hpages : pendingPages first = pendingPages second :=
    pendingPages_agree Request.DeadlineAgreeUpTo.page agree
  unfold nextPayment?
  rw [hpages]
  refine foldPayment_agree t (forall₂_map_of_forall _ _ _ ?_) (Or.inl rfl)
  intro page hpage
  have hpending : ∃ occurrence ∈ first.pending, occurrence.request.page = page :=
    pending_of_mem_pendingPages (hpages ▸ hpage)
  by_cases hle : deadlineTime first page ≤ t ∨ deadlineTime second page ≤ t
  · exact Or.inl (by
      simp only [Trigger.dueTime]
      rw [deadlineTime_agree hnow agree hpending hle])
  · push_neg at hle
    exact Or.inr ⟨hle.1, hle.2⟩

end
end PagingWithDelay.FIFO
