import PagingWithDelay.DeadlineLowerBound.Charging
import PagingWithDelay.Analysis.Adaptive

/-!
# Charging the online algorithm, in the language of `Model.lean`

The deadline drafts charge every processed request to a distinct online move.
In this model there is a second possibility — the algorithm may ignore a
request and pay delay instead — so the charge is a dichotomy
(`Charging.lean`): a request whose page is absent when it arrives is either
served by a fetch of that page inside its window, or it pays at least what its
curve has accrued by the end of that window.

`length_le_totalCost` below turns that into the bound the lower bound needs:

```text
number of requests ≤ ALG
```

for any instance all of whose requests are misses on arrival and are pairwise
*separated* — any two of them ask for different pages, or their charging
windows are disjoint.  Both halves of the dichotomy are then injective: two
fetch charges differ because a fetch event determines the pair (its time, the
page it fetched), and two delay charges are different summands of `totalDelay`.

Separation is exactly what the drafts' release rule provides: an auxiliary
request is issued at a page different from the distinguished one, and requests
issued in sequence get disjoint windows.
-/

namespace PagingWithDelay.DeadlineLowerBound

open Finset

noncomputable section

variable {Page : Type*} [DecidableEq Page]

/-! ## Fetch charges are injective -/

/-- Requests charged to fetch events of their own page at pairwise distinct
`(time, page)` pairs are at most as many as the fetches. -/
theorem length_le_fetchCount (schedule : Schedule Page) (requests : List (Request Page))
    (charge : Request Page → Time)
    (hcharge : ∀ request ∈ requests, ∃ event ∈ schedule.events,
      event.time = charge request ∧ event.fetched = request.page)
    (hsep : requests.Pairwise fun first second =>
      (charge first, first.page) ≠ (charge second, second.page)) :
    requests.length ≤ schedule.fetchCount := by
  have hnodup : (requests.map fun request => (charge request, request.page)).Nodup :=
    List.pairwise_map.mpr hsep
  have hsubset : (requests.map fun request => (charge request, request.page)) ⊆
      schedule.events.map fun event => (event.time, event.fetched) := by
    intro pair hpair
    obtain ⟨request, hrequest, rfl⟩ := List.mem_map.mp hpair
    obtain ⟨event, hevent, htime, hpage⟩ := hcharge request hrequest
    exact List.mem_map.mpr ⟨event, hevent, by rw [htime, hpage]⟩
  have hlength := (List.subperm_of_subset hnodup hsubset).length_le
  simpa [Schedule.fetchCount] using hlength

/-! ## The charge of a single request -/

/-- The two ways a request whose page is absent on arrival costs the schedule:
a fetch inside its window, or delay. -/
private def ChargedByFetch (schedule : Schedule Page) (window : Time)
    (request : Request Page) : Prop :=
  ∃ event ∈ schedule.events, event.fetched = request.page ∧
    request.arrival ≤ event.time ∧ event.time ≤ request.arrival + window

/-! ## The bound -/

/-- **Every separated miss costs the algorithm one unit.**  If every request of
`input` asks for a page the schedule does not hold when the request arrives, has
accrued at least one unit of delay by the end of its charging window, and any
two requests either ask for different pages or have disjoint charging windows,
then the schedule's total cost is at least the number of requests. -/
theorem length_le_totalCost {input : Instance Page} (schedule : Schedule Page)
    (feasible : schedule.Feasible input) (window : Request Page → Time)
    (hpenalty : ∀ request ∈ input.requests, 1 ≤ request.delay (window request))
    (hmiss : ∀ request ∈ input.requests,
      request.page ∉ schedule.cacheBefore request.arrival)
    (hsep : input.requests.Pairwise fun first second =>
      first.page ≠ second.page ∨ first.arrival + window first < second.arrival) :
    (input.requests.length : Cost) ≤ schedule.totalCost input := by
  classical
  set charged : Request Page → Bool :=
    fun request => decide (ChargedByFetch schedule (window request) request) with hcharged
  set hit := input.requests.filter charged with hhit
  set late := input.requests.filter (!charged ·) with hlate
  -- the fetch-charged requests are at most the fetches
  have hmem_hit : ∀ request ∈ hit, ChargedByFetch schedule (window request) request := by
    intro request hrequest
    exact of_decide_eq_true (List.mem_filter.mp hrequest).2
  -- pick, for every request, the time of the fetch that serves it
  have hchoice : ∀ request : Request Page, ∃ time : Time, request ∈ hit →
      ∃ chargedEvent ∈ schedule.events, chargedEvent.time = time ∧
        chargedEvent.fetched = request.page ∧ request.arrival ≤ chargedEvent.time ∧
          chargedEvent.time ≤ request.arrival + window request := by
    intro request
    by_cases hmem : request ∈ hit
    · obtain ⟨chargedEvent, hmemEvent, hpage, hafter, hbefore⟩ := hmem_hit request hmem
      exact ⟨chargedEvent.time, fun _ => ⟨chargedEvent, hmemEvent, rfl, hpage, hafter, hbefore⟩⟩
    · exact ⟨0, fun hcontra => absurd hcontra hmem⟩
  choose charge hchargeSpec using hchoice
  have hfetch : hit.length ≤ schedule.fetchCount := by
    refine length_le_fetchCount schedule hit charge
      (fun request hrequest => by
        obtain ⟨chargedEvent, hmemEvent, htime, hpage, _, _⟩ := hchargeSpec request hrequest
        exact ⟨chargedEvent, hmemEvent, htime, hpage⟩) ?_
    have hpairwise : hit.Pairwise fun first second =>
        first.page ≠ second.page ∨ first.arrival + window first < second.arrival :=
      hsep.sublist List.filter_sublist
    refine hpairwise.imp_of_mem ?_
    intro first second hfirst hsecond hcase hpair
    rcases hcase with hpages | hwindows
    · exact hpages (congrArg Prod.snd hpair)
    · obtain ⟨_, _, htimeFirst, _, _, hbefore⟩ := hchargeSpec first hfirst
      obtain ⟨_, _, htimeSecond, _, hafter, _⟩ := hchargeSpec second hsecond
      have hfirst_le : charge first ≤ first.arrival + window first := htimeFirst ▸ hbefore
      have hsecond_ge : second.arrival ≤ charge second := htimeSecond ▸ hafter
      have htimes : charge first = charge second := congrArg Prod.fst hpair
      exact absurd (htimes ▸ hfirst_le) (not_le_of_gt (hwindows.trans_le hsecond_ge))
  -- the remaining requests pay delay
  have hone : ∀ request ∈ late, 1 ≤ schedule.requestCost request := by
    intro request hrequest
    have hmemInput : request ∈ input.requests := (List.mem_filter.mp hrequest).1
    have hnot : ¬ ChargedByFetch schedule (window request) request := by
      have hbool := (List.mem_filter.mp hrequest).2
      simp only [hcharged, Bool.not_eq_true', decide_eq_false_iff_not] at hbool
      exact hbool
    rcases schedule.fetch_in_window_or_cost request
      (feasible.eventuallyServed request hmemInput) (hmiss request hmemInput)
      (window request) with hcharge | hcost
    · exact absurd hcharge hnot
    · exact (hpenalty request hmemInput).trans hcost
  have hlength_le : ∀ requests : List (Request Page),
      (∀ request ∈ requests, 1 ≤ schedule.requestCost request) →
        (requests.length : Cost) ≤ (requests.map schedule.requestCost).sum := by
    intro requests
    induction requests with
    | nil => intro _; simp
    | cons request rest ih =>
        intro hall
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        push_cast
        rw [add_comm (schedule.requestCost request)]
        exact add_le_add (ih fun other hother => hall other (List.mem_cons_of_mem _ hother))
          (hall request (List.mem_cons_self ..))
  have hdelay : (late.length : Cost) ≤ schedule.totalDelay input :=
    (hlength_le late hone).trans
      ((List.filter_sublist.map schedule.requestCost).sum_le_sum fun _ _ => zero_le _)
  -- the two families exhaust the requests
  have hsplit : input.requests.length = hit.length + late.length :=
    List.length_eq_length_filter_add charged
  rw [hsplit]
  calc ((hit.length + late.length : ℕ) : Cost)
      = (hit.length : Cost) + (late.length : Cost) := by push_cast; ring
    _ ≤ (schedule.fetchCount : Cost) + schedule.totalDelay input :=
        add_le_add (by exact_mod_cast hfetch) hdelay
    _ = schedule.totalCost input := rfl

/-! ## Releasing the next request

The adversary of the drafts always has a page to request: with `k + 2` pages
and a cache of `k`, at least two are uncovered, so one of them differs from the
distinguished page.  Onlineness then says that appending a request there does
not disturb what the algorithm did earlier, so earlier misses stay misses and
the new request is a miss too. -/

/-- At least two of the `k + 2` pages are missing from the cache at any time. -/
theorem two_le_card_uncovered {input : Instance Page} (schedule : Schedule Page)
    (feasible : schedule.Feasible input) {V : Finset Page} {k : ℕ}
    (hsize : input.cacheSize = k) (hcard : k + 2 ≤ V.card) (t : Time) :
    2 ≤ (V \ schedule.cacheBefore t).card := by
  have hcap : (schedule.cacheBefore t).card ≤ k := by
    rw [← hsize]
    exact schedule.cacheBefore_card_le input feasible t
  have hle := Finset.le_card_sdiff (schedule.cacheBefore t) V
  omega

/-- Hence a page to request: in `V`, uncovered, and different from the page the
adversary must leave alone. -/
theorem exists_uncovered_ne {input : Instance Page} (schedule : Schedule Page)
    (feasible : schedule.Feasible input) {V : Finset Page} {k : ℕ}
    (hsize : input.cacheSize = k) (hcard : k + 2 ≤ V.card) (t : Time) (avoid : Page) :
    ∃ page ∈ V, page ≠ avoid ∧ page ∉ schedule.cacheBefore t := by
  obtain ⟨first, hfirst, second, hsecond, hne⟩ :=
    Finset.one_lt_card.mp (two_le_card_uncovered schedule feasible hsize hcard t)
  by_cases havoid : first = avoid
  · refine ⟨second, (Finset.mem_sdiff.mp hsecond).1, ?_, (Finset.mem_sdiff.mp hsecond).2⟩
    rw [← havoid]
    exact fun heq => hne heq.symm
  · exact ⟨first, (Finset.mem_sdiff.mp hfirst).1, havoid, (Finset.mem_sdiff.mp hfirst).2⟩

/-- Appending a request leaves the cache before its arrival — and before any
earlier instant — exactly as it was.  This is
`Algorithm.Online.appendRequest_cacheBefore` at an arbitrary earlier time. -/
theorem appendRequest_cacheBefore_le {algorithm : Algorithm Page} (online : algorithm.Online)
    (input : Instance Page) (valid : input.Valid) (request : Request Page)
    (extendedValid : (input.appendRequest request).Valid) {t : Time}
    (ht : t ≤ request.arrival) :
    (algorithm (input.appendRequest request) extendedValid).cacheBefore t =
      (algorithm input valid).cacheBefore t := by
  apply online.cacheBefore_eq
  intro s hs
  exact input.appendRequest_upTo request (hs.trans_le ht)

/-- **One release.**  Every miss of the run so far is still a miss of the
extended run, and the new request is a miss as well. -/
theorem appendRequest_misses {algorithm : Algorithm Page} (online : algorithm.Online)
    (input : Instance Page) (valid : input.Valid) (request : Request Page)
    (extendedValid : (input.appendRequest request).Valid)
    (hearlier : ∀ other ∈ input.requests, other.arrival ≤ request.arrival)
    (hold : ∀ other ∈ input.requests,
      other.page ∉ (algorithm input valid).cacheBefore other.arrival)
    (hnew : request.page ∉ (algorithm input valid).cacheBefore request.arrival) :
    ∀ other ∈ (input.appendRequest request).requests,
      other.page ∉
        (algorithm (input.appendRequest request) extendedValid).cacheBefore other.arrival := by
  intro other hother
  rcases List.mem_append.mp hother with hother | hother
  · rw [appendRequest_cacheBefore_le online input valid request extendedValid
      (hearlier other hother)]
    exact hold other hother
  · rw [List.mem_singleton.mp hother,
      appendRequest_cacheBefore_le online input valid request extendedValid le_rfl]
    exact hnew

end
end PagingWithDelay.DeadlineLowerBound
