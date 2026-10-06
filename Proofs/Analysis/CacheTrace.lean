import Model
import Proofs.Analysis.Prefix

/-!
# Reading a cache trace by event index

`Schedule.cacheBefore` describes a trace by time.  For a counting argument it
is more convenient to describe it by event index: `cacheAfterCount schedule n`
is the cache after the first `n` events, and `eventCount schedule t` is the
number of events stamped no later than `t`.  For a chronological trace the two
descriptions agree.

Nothing here is specific to FIFO or to the competitive analysis; these are
facts about an arbitrary schedule.
-/

namespace PagingWithDelay.Analysis

open PagingWithDelay

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- Cache contents after the first `n` events of a trace, starting from its
initial cache. -/
def cacheAfterCount (schedule : Schedule Page) (n : ℕ) : Finset Page :=
  (schedule.events.take n).foldl (fun _ event => event.cacheAfter) schedule.initialCache

@[simp] theorem cacheAfterCount_zero (schedule : Schedule Page) :
    cacheAfterCount schedule 0 = schedule.initialCache := rfl

theorem cacheAfterCount_succ (schedule : Schedule Page) {n : ℕ}
    (hn : n < schedule.events.length) :
    cacheAfterCount schedule (n + 1) = schedule.events[n].cacheAfter := by
  unfold cacheAfterCount
  rw [List.take_add_one, List.getElem?_eq_getElem hn]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The number of events of a trace stamped no later than `t`. -/
def eventCount (schedule : Schedule Page) (t : Time) : ℕ :=
  schedule.events.countP fun event => decide (event.time ≤ t)

/-- The number of events of a trace stamped strictly before `t`. -/
def eventCountLT (schedule : Schedule Page) (t : Time) : ℕ :=
  schedule.events.countP fun event => decide (event.time < t)

theorem eventCount_le_length (schedule : Schedule Page) (t : Time) :
    eventCount schedule t ≤ schedule.events.length :=
  List.countP_le_length

theorem eventCount_mono (schedule : Schedule Page) {s t : Time} (hst : s ≤ t) :
    eventCount schedule s ≤ eventCount schedule t :=
  List.countP_mono_left fun _ _ h => by simp only [decide_eq_true_eq] at h ⊢; exact h.trans hst

theorem eventCountLT_le_eventCount (schedule : Schedule Page) {s t : Time} (hst : s ≤ t) :
    eventCountLT schedule s ≤ eventCount schedule t :=
  List.countP_mono_left fun _ _ h => by simp only [decide_eq_true_eq] at h ⊢; exact h.le.trans hst

theorem eventCount_le_eventCountLT (schedule : Schedule Page) {s t : Time} (hst : s < t) :
    eventCount schedule s ≤ eventCountLT schedule t :=
  List.countP_mono_left fun _ _ h => by simp only [decide_eq_true_eq] at h ⊢; exact h.trans_lt hst

section Chronological

variable {schedule : Schedule Page}
  (hchronological : schedule.events.Pairwise fun earlier later => earlier.time ≤ later.time)

include hchronological

private theorem pairwise_le (t : Time) :
    schedule.events.Pairwise fun x y =>
      (decide (y.time ≤ t)) = true → (decide (x.time ≤ t)) = true :=
  hchronological.imp fun hxy h => by simp only [decide_eq_true_eq] at h ⊢; exact hxy.trans h

private theorem pairwise_lt (t : Time) :
    schedule.events.Pairwise fun x y =>
      (decide (y.time < t)) = true → (decide (x.time < t)) = true :=
  hchronological.imp fun hxy h => by simp only [decide_eq_true_eq] at h ⊢; exact hxy.trans_lt h

private theorem time_le_iff_lt_eventCount {t : Time} {n : ℕ} (hn : n < schedule.events.length) :
    schedule.events[n].time ≤ t ↔ n < eventCount schedule t := by
  simpa using Analysis.lt_countP_iff (pairwise_le hchronological t) n hn

/-- An event inside the initial segment counted by `eventCount` is stamped in
time. -/
theorem time_le_of_lt_eventCount {t : Time} {n : ℕ} (hn : n < schedule.events.length)
    (hlt : n < eventCount schedule t) : schedule.events[n].time ≤ t :=
  (time_le_iff_lt_eventCount hchronological hn).mpr hlt

/-- Conversely an event stamped in time lies inside that initial segment. -/
theorem lt_eventCount_of_time_le {t : Time} {n : ℕ} (hn : n < schedule.events.length)
    (hle : schedule.events[n].time ≤ t) : n < eventCount schedule t :=
  (time_le_iff_lt_eventCount hchronological hn).mp hle

/-- The cache strictly before `t` is the cache after the events preceding `t`. -/
theorem cacheBefore_eq_cacheAfterCount (t : Time) :
    schedule.cacheBefore t = cacheAfterCount schedule (eventCountLT schedule t) := by
  unfold Schedule.cacheBefore cacheAfterCount eventCountLT
  simp [← Analysis.filter_eq_take_countP (Analysis.pairwise_lt hchronological t), List.foldl_filter]

end Chronological

/-- The local consistency condition of a trace, read at one event index. -/
theorem validTransitions_getElem {previous : Finset Page} :
    ∀ {events : List (FetchEvent Page)}, Schedule.ValidTransitionsFrom previous events →
      ∀ (n : ℕ) (hn : n < events.length),
        events[n].fetched ∈ events[n].cacheAfter ∧
          events[n].cacheAfter \
            ((events.take n).foldl (fun _ event => event.cacheAfter) previous) =
            {events[n].fetched}
  | [], _, _, hn => absurd hn (by simp)
  | event :: rest, h, 0, _ => ⟨h.1, h.2.1⟩
  | event :: rest, h, n + 1, hn => by
      simpa using validTransitions_getElem h.2.2 n (by simpa using hn)

theorem fetched_mem_cacheAfterCount (schedule : Schedule Page)
    (htransitions : Schedule.ValidTransitionsFrom schedule.initialCache schedule.events)
    {n : ℕ}
    (hn : n < schedule.events.length) :
    schedule.events[n].fetched ∈ cacheAfterCount schedule (n + 1) := by
  rw [cacheAfterCount_succ schedule hn]
  exact (validTransitions_getElem htransitions n hn).1

end

end PagingWithDelay.Analysis
