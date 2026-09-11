import PagingWithDelay.DeadlineLowerBound.Certificate

/-!
# From the certificate's move lists to `Model.lean` schedules

`Offline.lean` describes offline schedules as a start configuration plus a list
of timed moves, because that is the language the deadline drafts are written
in.  Nothing may be trusted in that language.  This file discharges the
translation: `buildSchedule` turns a move list into a `Schedule` of
`Model.lean`, and `feasible_buildSchedule` proves it `Schedule.Feasible` for an
instance whose requests the moves serve, with

```text
totalCost = cacheSize + (number of moves)
```

The additive `cacheSize` is forced by the model and is not an artefact of the
translation: `Model.lean` starts every schedule with an empty cache
(`ValidTransitionsFrom ∅`), whereas the drafts start both schedules on a common
set of `k` nodes.  Those `k` fetches are stamped at time `0`, which is why the
translation asks for every request to arrive, and every move to happen, strictly
after `0`.

The delay side costs nothing: a request whose delay curve still vanishes at the
end of its window contributes `0`, whether it is served by a cache hit at
arrival or by a fetch inside the window.  That is the only property of a
"deadline-shaped" curve the offline side uses.
-/

namespace PagingWithDelay.DeadlineLowerBound

open Finset

noncomputable section

variable {Page : Type*} [DecidableEq Page]

/-! ## Two model lemmas

Both are about `Model.lean` alone; the second is the counterpart of
`Schedule.requestCost_eq_zero_of_mem_cacheBefore` for service by a fetch. -/

/-- Any fetch of the requested page at or after its arrival is a service
candidate. -/
theorem mem_serviceCandidates_of_mem_events (schedule : Schedule Page) (request : Request Page)
    {event : FetchEvent Page} (hevent : event ∈ schedule.events)
    (harrival : request.arrival ≤ event.time) (hpage : request.page = event.fetched) :
    event.time ∈ schedule.serviceCandidates request := by
  have hfiltered : event ∈ schedule.events.filter fun candidate =>
      request.arrival ≤ candidate.time ∧ request.page = candidate.fetched := by
    simp only [List.mem_filter]
    exact ⟨hevent, by simp [harrival, hpage]⟩
  have htime : event.time ∈ ((schedule.events.filter fun candidate =>
      request.arrival ≤ candidate.time ∧ request.page = candidate.fetched).map
        FetchEvent.time).toFinset := by
    rw [List.mem_toFinset]
    exact List.mem_map.mpr ⟨event, hfiltered, rfl⟩
  unfold Schedule.serviceCandidates
  split
  · exact Finset.mem_insert_of_mem htime
  · exact htime

/-- A service candidate bounds the delay cost. -/
theorem requestCost_le_of_mem_serviceCandidates (schedule : Schedule Page)
    (request : Request Page) {time : Time}
    (hmem : time ∈ schedule.serviceCandidates request) :
    schedule.requestCost request ≤ request.delay (time - request.arrival) := by
  have hne : (schedule.serviceCandidates request).Nonempty := ⟨time, hmem⟩
  have hservice : schedule.serviceTime request =
      some ((schedule.serviceCandidates request).min' hne) := by
    rw [Schedule.serviceTime, dif_pos hne]
  rw [Schedule.requestCost, Schedule.serviceDelay, hservice]
  exact request.delay_mono (tsub_le_tsub_right (Finset.min'_le _ _ hmem) _)

/-- A page in the cache when the request arrives is served at once, at zero
delay.  (`EventLoop/ServiceBridge.lean` proves this too; it is repeated here so
that the translation depends on `Model.lean` alone.) -/
theorem requestCost_eq_zero_of_hit (schedule : Schedule Page) (request : Request Page)
    (hhit : request.page ∈ schedule.cacheBefore request.arrival) :
    schedule.requestCost request = 0 := by
  have hmem : request.arrival ∈ schedule.serviceCandidates request := by
    unfold Schedule.serviceCandidates
    rw [if_pos hhit]
    exact Finset.mem_insert_self _ _
  refine le_antisymm ?_ (zero_le _)
  calc schedule.requestCost request
      ≤ request.delay (request.arrival - request.arrival) :=
        requestCost_le_of_mem_serviceCandidates _ _ hmem
    _ = 0 := by rw [tsub_self, request.delay_zero]

/-! ## Building the schedule -/

/-- The cache after filling an empty cache with `pages`. -/
def fillCache (pages : List Page) (cache : Finset Page) : Finset Page :=
  pages.foldl (fun current page => insert page current) cache

/-- The fetch events that fill the cache with `pages`, all stamped `0`. -/
def fillEvents : List Page → Finset Page → List (FetchEvent Page)
  | [], _ => []
  | page :: rest, cache =>
      ⟨0, page, insert page cache⟩ :: fillEvents rest (insert page cache)

/-- The fetch events of a move list. -/
def moveEvents : Finset Page → List (Move Page) → List (FetchEvent Page)
  | _, [] => []
  | cache, mv :: rest =>
      ⟨mv.time, mv.fetched, applyMove cache mv⟩ :: moveEvents (applyMove cache mv) rest

/-- The `Model.lean` schedule of an offline run: fill the empty cache with the
start configuration at time `0`, then make the moves. -/
def buildSchedule (start : Finset Page) (moves : List (Move Page)) : Schedule Page :=
  ⟨fillEvents start.toList ∅ ++ moveEvents start moves⟩

theorem fillCache_union (pages : List Page) (cache : Finset Page) :
    fillCache pages cache = cache ∪ pages.toFinset := by
  induction pages generalizing cache with
  | nil => simp [fillCache]
  | cons page rest ih =>
      simp only [fillCache, List.foldl_cons] at ih ⊢
      rw [ih]
      ext y
      simp [Finset.mem_union, Finset.mem_insert]

@[simp] theorem fillCache_toList (start : Finset Page) : fillCache start.toList ∅ = start := by
  rw [fillCache_union]
  simp

theorem length_fillEvents (pages : List Page) (cache : Finset Page) :
    (fillEvents pages cache).length = pages.length := by
  induction pages generalizing cache with
  | nil => rfl
  | cons page rest ih => simp [fillEvents, ih]

theorem length_moveEvents (cache : Finset Page) (moves : List (Move Page)) :
    (moveEvents cache moves).length = moves.length := by
  induction moves generalizing cache with
  | nil => rfl
  | cons mv rest ih => simp [moveEvents, ih]

theorem time_of_mem_fillEvents {pages : List Page} {cache : Finset Page}
    {event : FetchEvent Page} (hevent : event ∈ fillEvents pages cache) : event.time = 0 := by
  induction pages generalizing cache with
  | nil => simp [fillEvents] at hevent
  | cons page rest ih =>
      rcases List.mem_cons.mp hevent with rfl | hevent
      · rfl
      · exact ih hevent

theorem exists_move_of_mem_moveEvents {cache : Finset Page} {moves : List (Move Page)}
    {event : FetchEvent Page} (hevent : event ∈ moveEvents cache moves) :
    ∃ mv ∈ moves, event.time = mv.time ∧ event.fetched = mv.fetched := by
  induction moves generalizing cache with
  | nil => simp [moveEvents] at hevent
  | cons mv rest ih =>
      rcases List.mem_cons.mp hevent with rfl | hevent
      · exact ⟨mv, List.mem_cons_self .., rfl, rfl⟩
      · obtain ⟨candidate, hcandidate, htime, hpage⟩ := ih hevent
        exact ⟨candidate, List.mem_cons_of_mem _ hcandidate, htime, hpage⟩

theorem mem_moveEvents {cache : Finset Page} {moves : List (Move Page)} {mv : Move Page}
    (hmv : mv ∈ moves) :
    ∃ event ∈ moveEvents cache moves, event.time = mv.time ∧ event.fetched = mv.fetched := by
  induction moves generalizing cache with
  | nil => simp at hmv
  | cons head rest ih =>
      rcases List.mem_cons.mp hmv with rfl | hmv
      · exact ⟨⟨mv.time, mv.fetched, applyMove cache mv⟩, List.mem_cons_self .., rfl, rfl⟩
      · obtain ⟨event, hevent, htime, hpage⟩ := ih (cache := applyMove cache head) hmv
        exact ⟨event, List.mem_cons_of_mem _ hevent, htime, hpage⟩

/-! ## The cache before a time -/

theorem foldl_late (t : Time) :
    ∀ (cache : Finset Page) (moves : List (Move Page)) (init : Finset Page),
      (∀ mv ∈ moves, ¬ mv.time < t) →
      (moveEvents cache moves).foldl
          (fun current event => if event.time < t then event.cacheAfter else current) init = init := by
  intro cache moves
  induction moves generalizing cache with
  | nil => intro init _; rfl
  | cons mv rest ih =>
      intro init hlate
      simp only [moveEvents, List.foldl_cons,
        if_neg (hlate mv (List.mem_cons_self ..))]
      exact ih _ init fun candidate hcandidate =>
        hlate candidate (List.mem_cons_of_mem _ hcandidate)

theorem foldl_moveEvents (t : Time) :
    ∀ (cache : Finset Page) (moves : List (Move Page)),
      moves.Pairwise (fun earlier later => earlier.time < later.time) →
      (moveEvents cache moves).foldl
          (fun current event => if event.time < t then event.cacheAfter else current) cache =
        cacheAfter cache (moves.filter fun mv => decide (mv.time < t)) := by
  intro cache moves
  induction moves generalizing cache with
  | nil => intro _; rfl
  | cons mv rest ih =>
      intro hchrono
      rw [List.pairwise_cons] at hchrono
      by_cases htime : mv.time < t
      · simp only [moveEvents, List.foldl_cons, if_pos htime, List.filter_cons,
          decide_eq_true htime, if_pos]
        exact ih _ hchrono.2
      · have hlate : ∀ candidate ∈ mv :: rest, ¬ candidate.time < t := by
          intro candidate hcandidate
          rcases List.mem_cons.mp hcandidate with rfl | hcandidate
          · exact htime
          · exact fun hlt => htime ((hchrono.1 candidate hcandidate).trans hlt)
        rw [List.filter_eq_nil_iff.mpr (fun candidate hcandidate => by
          simpa using hlate candidate hcandidate)]
        simp only [moveEvents, List.foldl_cons, if_neg htime]
        exact foldl_late t _ rest cache fun candidate hcandidate =>
          hlate candidate (List.mem_cons_of_mem _ hcandidate)

theorem foldl_fillEvents {t : Time} (ht : 0 < t) :
    ∀ (pages : List Page) (cache init : Finset Page), pages ≠ [] →
      (fillEvents pages cache).foldl
          (fun current event => if event.time < t then event.cacheAfter else current) init =
        fillCache pages cache := by
  intro pages
  induction pages with
  | nil => intro _ _ hne; exact absurd rfl hne
  | cons page rest ih =>
      intro cache init _
      simp only [fillEvents, List.foldl_cons, if_pos ht]
      cases rest with
      | nil => rfl
      | cons next more =>
          rw [ih (insert page cache) (insert page cache) (by simp)]
          rfl

/-- The translation computes the same cache as the offline model. -/
theorem cacheBefore_buildSchedule {start : Finset Page} {moves : List (Move Page)}
    (hstart : start.Nonempty)
    (hchrono : moves.Pairwise fun earlier later => earlier.time < later.time)
    {t : Time} (ht : 0 < t) :
    (buildSchedule start moves).cacheBefore t = cacheBefore start moves t := by
  have hlist : start.toList ≠ [] := by
    simpa using hstart.ne_empty ∘ Finset.toList_eq_nil.mp
  unfold Schedule.cacheBefore buildSchedule
  rw [List.foldl_append, foldl_fillEvents ht start.toList ∅ ∅ hlist, fillCache_toList,
    foldl_moveEvents t start moves hchrono]
  rfl

/-! ## Feasibility of the built schedule -/

/-- The cache after a list of fetch events. -/
def lastCache (previous : Finset Page) : List (FetchEvent Page) → Finset Page
  | [] => previous
  | event :: rest => lastCache event.cacheAfter rest

theorem validTransitionsFrom_append {previous : Finset Page} :
    ∀ {first second : List (FetchEvent Page)},
      Schedule.ValidTransitionsFrom previous first →
      Schedule.ValidTransitionsFrom (lastCache previous first) second →
      Schedule.ValidTransitionsFrom previous (first ++ second) := by
  intro first
  induction first generalizing previous with
  | nil => intro second _ hsecond; exact hsecond
  | cons event rest ih =>
      rintro second ⟨hmem, hdiff, hrest⟩ hsecond
      exact ⟨hmem, hdiff, ih hrest hsecond⟩

theorem lastCache_fillEvents : ∀ (pages : List Page) (cache : Finset Page),
    lastCache cache (fillEvents pages cache) = fillCache pages cache := by
  intro pages
  induction pages with
  | nil => intro _; rfl
  | cons page rest ih => intro cache; exact ih (insert page cache)

theorem lastCache_moveEvents : ∀ (cache : Finset Page) (moves : List (Move Page)),
    lastCache cache (moveEvents cache moves) = cacheAfter cache moves := by
  intro cache moves
  induction moves generalizing cache with
  | nil => rfl
  | cons mv rest ih => exact ih (applyMove cache mv)

theorem insert_sdiff_self {cache : Finset Page} {page : Page} (hpage : page ∉ cache) :
    insert page cache \ cache = {page} := by
  ext y
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | hy, hnot⟩
    · rfl
    · exact absurd hy hnot
  · rintro rfl
    exact ⟨Or.inl rfl, hpage⟩

theorem applyMove_sdiff {cache : Finset Page} {mv : Move Page} (hfetch : mv.fetched ∉ cache) :
    applyMove cache mv \ cache = {mv.fetched} := by
  ext y
  simp only [applyMove, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase,
    Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | ⟨_, hy⟩, hnot⟩
    · rfl
    · exact absurd hy hnot
  · rintro rfl
    exact ⟨Or.inl rfl, hfetch⟩

theorem validTransitions_fillEvents : ∀ (pages : List Page) (cache : Finset Page),
    pages.Nodup → (∀ page ∈ pages, page ∉ cache) →
      Schedule.ValidTransitionsFrom cache (fillEvents pages cache) := by
  intro pages
  induction pages with
  | nil => intro _ _ _; trivial
  | cons page rest ih =>
      intro cache hnodup hfresh
      rw [List.nodup_cons] at hnodup
      refine ⟨Finset.mem_insert_self _ _,
        insert_sdiff_self (hfresh page (List.mem_cons_self ..)), ?_⟩
      refine ih (insert page cache) hnodup.2 ?_
      intro other hother
      rw [Finset.mem_insert]
      push_neg
      exact ⟨fun heq => hnodup.1 (heq ▸ hother),
        hfresh other (List.mem_cons_of_mem _ hother)⟩

theorem validTransitions_moveEvents : ∀ (cache : Finset Page) (moves : List (Move Page)),
    ValidMoves cache moves → Schedule.ValidTransitionsFrom cache (moveEvents cache moves) := by
  intro cache moves
  induction moves generalizing cache with
  | nil => intro _; trivial
  | cons mv rest ih =>
      rintro ⟨hevict, hfetch, hrest⟩
      exact ⟨Finset.mem_insert_self _ _, applyMove_sdiff hfetch, ih _ hrest⟩

theorem subset_fillCache (pages : List Page) (cache : Finset Page) :
    cache ⊆ fillCache pages cache := by
  rw [fillCache_union]
  exact Finset.subset_union_left

theorem cacheAfter_subset_of_mem_fillEvents : ∀ (pages : List Page) (cache : Finset Page)
    (event : FetchEvent Page), event ∈ fillEvents pages cache →
      event.cacheAfter ⊆ fillCache pages cache := by
  intro pages
  induction pages with
  | nil => intro _ _ hevent; simp [fillEvents] at hevent
  | cons page rest ih =>
      intro cache event hevent
      rcases List.mem_cons.mp hevent with rfl | hevent
      · exact subset_fillCache rest (insert page cache)
      · exact ih (insert page cache) event hevent

theorem card_of_mem_moveEvents : ∀ (cache : Finset Page) (moves : List (Move Page)),
    ValidMoves cache moves → ∀ event ∈ moveEvents cache moves,
      event.cacheAfter.card = cache.card := by
  intro cache moves
  induction moves generalizing cache with
  | nil => intro _ _ hevent; simp [moveEvents] at hevent
  | cons mv rest ih =>
      rintro ⟨hevict, hfetch, hrest⟩ event hevent
      rcases List.mem_cons.mp hevent with rfl | hevent
      · exact card_applyMove hevict hfetch
      · rw [ih _ hrest event hevent]
        exact card_applyMove hevict hfetch

theorem pairwise_fillEvents : ∀ (pages : List Page) (cache : Finset Page),
    (fillEvents pages cache).Pairwise fun earlier later => earlier.time ≤ later.time := by
  intro pages
  induction pages with
  | nil => intro _; exact List.Pairwise.nil
  | cons page rest ih =>
      intro cache
      exact List.pairwise_cons.mpr ⟨fun _ _ => zero_le _, ih (insert page cache)⟩

theorem pairwise_moveEvents : ∀ (cache : Finset Page) (moves : List (Move Page)),
    moves.Pairwise (fun earlier later => earlier.time < later.time) →
      (moveEvents cache moves).Pairwise fun earlier later => earlier.time ≤ later.time := by
  intro cache moves
  induction moves generalizing cache with
  | nil => intro _; exact List.Pairwise.nil
  | cons mv rest ih =>
      intro hchrono
      rw [List.pairwise_cons] at hchrono
      refine List.pairwise_cons.mpr ⟨?_, ih _ hchrono.2⟩
      intro event hevent
      obtain ⟨candidate, hcandidate, htime, _⟩ := exists_move_of_mem_moveEvents hevent
      rw [htime]
      exact (hchrono.1 candidate hcandidate).le

/-! ## Service -/

theorem serves_buildSchedule {start : Finset Page} {moves : List (Move Page)}
    (hstart : start.Nonempty)
    (hchrono : moves.Pairwise fun earlier later => earlier.time < later.time)
    (request : Request Page) {deadline : Time} (harrival : 0 < request.arrival)
    (hzero : request.delay (deadline - request.arrival) = 0)
    (hserves : Serves start moves ⟨request.page, request.arrival, deadline⟩) :
    ((buildSchedule start moves).serviceCandidates request).Nonempty ∧
      (buildSchedule start moves).requestCost request = 0 := by
  rcases hserves with hhit | ⟨mv, hmv, hpage, hafter, hbefore⟩
  · have hcache : request.page ∈ (buildSchedule start moves).cacheBefore request.arrival := by
      rw [cacheBefore_buildSchedule hstart hchrono harrival]
      exact hhit
    refine ⟨⟨request.arrival, ?_⟩,
      requestCost_eq_zero_of_hit _ _ hcache⟩
    unfold Schedule.serviceCandidates
    rw [if_pos hcache]
    exact Finset.mem_insert_self _ _
  · obtain ⟨event, hevent, htime, hfetched⟩ := mem_moveEvents (cache := start) hmv
    have hmem : event ∈ (buildSchedule start moves).events :=
      List.mem_append_right _ hevent
    have hcandidate : event.time ∈ (buildSchedule start moves).serviceCandidates request :=
      mem_serviceCandidates_of_mem_events _ _ hmem (by rw [htime]; exact hafter)
        (by rw [hfetched, hpage])
    refine ⟨⟨event.time, hcandidate⟩, le_antisymm ?_ (zero_le _)⟩
    calc (buildSchedule start moves).requestCost request
        ≤ request.delay (event.time - request.arrival) :=
          requestCost_le_of_mem_serviceCandidates _ _ hcandidate
      _ ≤ request.delay (deadline - request.arrival) := by
          refine request.delay_mono (tsub_le_tsub_right ?_ _)
          rw [htime]
          exact hbefore
      _ = 0 := hzero

/-! ## The translation theorem -/

/-- **The certificate's schedules are `Model.lean` schedules.**  A valid move
list whose moves all happen after time `0`, serving every request of `input`
inside its window, becomes a feasible schedule of cost exactly
`cacheSize + (number of moves)`. -/
theorem feasible_buildSchedule {k : ℕ} {start : Finset Page} {moves : List (Move Page)}
    {input : Instance Page} (hsize : input.cacheSize = k) (hcard : start.card = k)
    (hstart : start.Nonempty) (hvalid : ValidMoves start moves)
    (hchrono : moves.Pairwise fun earlier later => earlier.time < later.time)
    (deadline : Request Page → Time)
    (harrival : ∀ request ∈ input.requests, 0 < request.arrival)
    (hzero : ∀ request ∈ input.requests,
      request.delay (deadline request - request.arrival) = 0)
    (hserves : ∀ request ∈ input.requests,
      Serves start moves ⟨request.page, request.arrival, deadline request⟩) :
    (buildSchedule start moves).Feasible input ∧
      (buildSchedule start moves).totalCost input = ((k + moves.length : ℕ) : Cost) := by
  have hfill : fillCache start.toList ∅ = start := fillCache_toList start
  have hservice : ∀ request ∈ input.requests,
      ((buildSchedule start moves).serviceCandidates request).Nonempty ∧
        (buildSchedule start moves).requestCost request = 0 := by
    intro request hrequest
    exact serves_buildSchedule hstart hchrono request (harrival request hrequest)
      (hzero request hrequest) (hserves request hrequest)
  refine ⟨⟨?_, ?_, ?_, fun request hrequest => (hservice request hrequest).1⟩, ?_⟩
  · -- chronological
    rw [buildSchedule]
    refine List.pairwise_append.mpr ⟨pairwise_fillEvents _ _, pairwise_moveEvents _ _ hchrono, ?_⟩
    intro earlier hearlier later _
    rw [time_of_mem_fillEvents hearlier]
    exact zero_le _
  · -- valid transitions
    refine validTransitionsFrom_append
      (validTransitions_fillEvents start.toList ∅ (Finset.nodup_toList start) (by simp)) ?_
    rw [lastCache_fillEvents, hfill]
    exact validTransitions_moveEvents start moves hvalid
  · -- capacity
    intro event hevent
    rw [hsize]
    rcases List.mem_append.mp hevent with hevent | hevent
    · calc event.cacheAfter.card
          ≤ (fillCache start.toList ∅).card :=
            Finset.card_le_card (cacheAfter_subset_of_mem_fillEvents _ _ event hevent)
        _ = k := by rw [hfill, hcard]
    · rw [card_of_mem_moveEvents start moves hvalid event hevent, hcard]
  · -- cost
    have hdelay : (buildSchedule start moves).totalDelay input = 0 := by
      refine List.sum_eq_zero ?_
      intro cost hcost
      obtain ⟨request, hrequest, rfl⟩ := List.mem_map.mp hcost
      exact (hservice request hrequest).2
    rw [Schedule.totalCost, hdelay, add_zero, Schedule.fetchCount, buildSchedule]
    simp [length_fillEvents, length_moveEvents, hcard]

/-! ## Deadline-shaped requests

`Model.lean` has no hard deadlines: a delay curve is continuous and unbounded.
The stand-in is a curve that stays at zero for the length of the window and
then grows.  Only `delay_window` is used by the offline side; `delay_penalty`
is what the online side charges against (see `Charging.lean`). -/

/-- Zero delay until `window` has elapsed, then growth at `rate`.

The rate matters.  A hard deadline penalises any overshoot; a continuous curve
charges `rate * overshoot`, so an adversary that must charge a whole unit
within an overshoot of `ε` has to pick `rate ≥ 1 / ε`.  That is what lets the
construction squeeze arbitrarily many chargeable requests into a bounded
interval, which the drafts get for free from hard deadlines. -/
def deadlineRequest (page : Page) (arrival window rate : Time) (hrate : 0 < rate) :
    Request Page where
  page := page
  arrival := arrival
  delay := fun wait => rate * (wait - window)
  delay_continuous := continuous_const.mul (continuous_id.sub continuous_const)
  delay_mono := fun first second hle =>
    show rate * (first - window) ≤ rate * (second - window) by gcongr
  delay_zero := by simp
  delay_unbounded := fun bound => ⟨window + bound / rate, by
    rw [add_tsub_cancel_left, mul_div_cancel₀ _ (ne_of_gt hrate)]⟩

omit [DecidableEq Page] in
@[simp] theorem deadlineRequest_page (page : Page) (arrival window rate : Time)
    (hrate : 0 < rate) : (deadlineRequest page arrival window rate hrate).page = page := rfl

omit [DecidableEq Page] in
@[simp] theorem deadlineRequest_arrival (page : Page) (arrival window rate : Time)
    (hrate : 0 < rate) :
    (deadlineRequest page arrival window rate hrate).arrival = arrival := rfl

omit [DecidableEq Page] in
/-- Inside its window the request is free: this is the offline side's `hzero`. -/
theorem deadlineRequest_delay_window (page : Page) (arrival window rate : Time)
    (hrate : 0 < rate) :
    (deadlineRequest page arrival window rate hrate).delay
      ((arrival + window) - arrival) = 0 := by
  simp [deadlineRequest]

omit [DecidableEq Page] in
/-- A unit of delay is accrued by the time the window has been overshot by
`overshoot`, provided the rate is steep enough: this is the online side's
`hpenalty`. -/
theorem deadlineRequest_delay_penalty (page : Page) (arrival window rate overshoot : Time)
    (hrate : 0 < rate) (hsteep : 1 ≤ rate * overshoot) :
    1 ≤ (deadlineRequest page arrival window rate hrate).delay (window + overshoot) := by
  simpa [deadlineRequest] using hsteep

/-! ## The certificate's bound on the optimum, in the language of `Model.lean` -/

/-- **The offline certificate, discharged into the trusted definitions.**  At
any checkpoint, the certificate yields a schedule that `Model.lean` calls
feasible for the instance it has served, of total cost at most
`cacheSize + m + 1`.

This is the drafts' `OPT ≤ m_T + 1`, plus the `cacheSize` that `Model.lean`'s
empty initial cache costs any schedule.  The hypotheses are: the instance's
cache has the size of the certificate's configurations (`hsize`, `hcard`), every
request arrives after time `0` (`harrival`), every request is free inside its
window (`hzero`), and every request of the instance is one the certificate has
served (`hmem`). -/
theorem certificate_totalCost_le {k : ℕ} {V start : Finset Page}
    {processed : List (Window Page)} {alpha : Window Page} {c : Page} {L : Finset Page}
    {q : Option Page} {m : ℕ} {now : Time}
    (hcert : Certificate V start processed alpha c L q m now)
    {z : Page} (hz : z ∈ L) (hne : (V \ {c, z}).Nonempty)
    {input : Instance Page} (hsize : input.cacheSize = k) (hcard : start.card = k)
    (hstart : start.Nonempty) (deadline : Request Page → Time)
    (harrival : ∀ request ∈ input.requests, 0 < request.arrival)
    (hzero : ∀ request ∈ input.requests,
      request.delay (deadline request - request.arrival) = 0)
    (hmem : ∀ request ∈ input.requests,
      (⟨request.page, request.arrival, deadline request⟩ : Window Page) ∈ alpha :: processed) :
    ∃ schedule : Schedule Page, schedule.Feasible input ∧
      schedule.totalCost input ≤ ((k + (m + 1) : ℕ) : Cost) := by
  obtain ⟨t, cfg, moves, hvalid, hchrono, _, hlength, hserves, _⟩ :=
    hcert.exists_final_schedule hz hne
  obtain ⟨hfeasible, hcost⟩ :=
    feasible_buildSchedule hsize hcard hstart hvalid hchrono deadline harrival hzero
      (fun request hrequest => hserves _ (hmem request hrequest))
  refine ⟨buildSchedule start moves, hfeasible, ?_⟩
  rw [hcost]
  exact_mod_cast Nat.add_le_add_left hlength k

/-! ## The translation is not vacuous

Every hypothesis of `feasible_buildSchedule` holds at once for a one-page
cache serving one deadline-shaped request, and the cost is the promised one:
`1` for filling the empty cache, and no delay. -/

example :
    (buildSchedule ({0} : Finset ℕ) []).Feasible ⟨1, [deadlineRequest 0 1 1 1 zero_lt_one]⟩ ∧
      (buildSchedule ({0} : Finset ℕ) []).totalCost ⟨1, [deadlineRequest 0 1 1 1 zero_lt_one]⟩
        = ((1 + 0 : ℕ) : Cost) := by
  refine feasible_buildSchedule (k := 1) rfl (by simp) ⟨0, by simp⟩ trivial
    List.Pairwise.nil (fun request => request.arrival + 1) ?_ ?_ ?_
  · intro request hrequest
    simp only [List.mem_singleton] at hrequest
    subst hrequest
    norm_num
  · intro request hrequest
    simp only [List.mem_singleton] at hrequest
    subst hrequest
    simp [deadlineRequest]
  · intro request hrequest
    simp only [List.mem_singleton] at hrequest
    subst hrequest
    exact Or.inl (by simp [cacheBefore, cacheAfter, deadlineRequest])

end
end PagingWithDelay.DeadlineLowerBound
