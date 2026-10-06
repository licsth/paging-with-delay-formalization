import Proofs.DeadlineLowerBound.Charging
import Proofs.Analysis.Adaptive

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
  -- the requests served by a fetch inside their charging window
  set charged : Request Page → Bool := fun request => decide (∃ event ∈ schedule.events,
    event.fetched = request.page ∧ request.arrival ≤ event.time ∧
      event.time ≤ request.arrival + window request) with hcharged
  -- pick, for every such request, the time of that fetch
  have hchoice : ∀ request : Request Page, ∃ time : Time, charged request →
      ∃ event ∈ schedule.events, event.time = time ∧ event.fetched = request.page ∧
        request.arrival ≤ time ∧ time ≤ request.arrival + window request := by
    intro request
    by_cases h : charged request
    · obtain ⟨event, hevent, hpage, hafter, hbefore⟩ := of_decide_eq_true h
      exact ⟨event.time, fun _ => ⟨event, hevent, rfl, hpage, hafter, hbefore⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose charge hcharge using hchoice
  -- they are at most the fetches
  have hfetch : (input.requests.filter charged).length ≤ schedule.fetchCount := by
    refine length_le_fetchCount schedule _ charge (fun request hrequest => ?_) ?_
    · obtain ⟨event, hevent, htime, hpage, -⟩ :=
        hcharge request (List.mem_filter.mp hrequest).2
      exact ⟨event, hevent, htime, hpage⟩
    · refine (hsep.sublist List.filter_sublist).imp_of_mem fun hfirst hsecond hcase hpair => ?_
      obtain ⟨-, -, -, -, -, hbefore⟩ := hcharge _ (List.mem_filter.mp hfirst).2
      obtain ⟨-, -, -, -, hafter, -⟩ := hcharge _ (List.mem_filter.mp hsecond).2
      rcases hcase with hpages | hwindows
      · exact hpages (congrArg Prod.snd hpair)
      · exact (hbefore.trans_lt (hwindows.trans_le hafter)).ne (congrArg Prod.fst hpair)
  -- the remaining requests pay delay
  have hdelay : ((input.requests.filter (!charged ·)).length : Cost) ≤
      schedule.totalDelay input := by
    have hone : ∀ cost ∈ (input.requests.filter (!charged ·)).map schedule.requestCost,
        1 ≤ cost := by
      simp only [List.mem_map, List.mem_filter]
      rintro _ ⟨request, ⟨hrequest, hnot⟩, rfl⟩
      rcases schedule.fetch_in_window_or_cost request (feasible.eventuallyServed request hrequest)
        (hmiss request hrequest) (window request) with hfetch | hcost
      · simp [hcharged, hfetch] at hnot
      · exact (hpenalty request hrequest).trans hcost
    simpa using (List.card_nsmul_le_sum _ 1 hone).trans
      ((List.filter_sublist.map schedule.requestCost).sum_le_sum fun _ _ => zero_le _)
  -- the two families exhaust the requests
  rw [List.length_eq_length_filter_add charged, Nat.cast_add, Schedule.totalCost]
  exact add_le_add (by exact_mod_cast hfetch) hdelay

/-! ## Releasing the next request

The adversary of the drafts always has a page to request: with `k + 2` pages
and a cache of `k`, at least two are uncovered, so one of them differs from the
distinguished page.  Onlineness then says that appending a request there does
not disturb what the algorithm did earlier, so earlier misses stay misses and
the new request is a miss too. -/

/-- At least two of the `k + 2` pages are missing from the cache at any time,
hence a page to request: in `V`, uncovered, and different from the page the
adversary must leave alone. -/
theorem exists_uncovered_ne {input : Instance Page} (schedule : Schedule Page)
    (feasible : schedule.Feasible input) {V : Finset Page} {k : ℕ}
    (hsize : input.cacheSize = k) (hcard : k + 2 ≤ V.card) (t : Time) (avoid : Page) :
    ∃ page ∈ V, page ≠ avoid ∧ page ∉ schedule.cacheBefore t := by
  have hcap := hsize ▸ schedule.cacheBefore_card_le input feasible t
  have hle := Finset.le_card_sdiff (schedule.cacheBefore t) V
  obtain ⟨first, hfirst, second, hsecond, hne⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (V \ schedule.cacheBefore t).card)
  rw [Finset.mem_sdiff] at hfirst hsecond
  by_cases havoid : first = avoid
  · exact ⟨second, hsecond.1, havoid ▸ hne.symm, hsecond.2⟩
  · exact ⟨first, hfirst.1, havoid, hfirst.2⟩

/-- Appending a request leaves the cache before its arrival — and before any
earlier instant — exactly as it was.  This is
`Algorithm.Online.appendRequest_cacheBefore` at an arbitrary earlier time. -/
theorem appendRequest_cacheBefore_le {algorithm : Algorithm Page} (online : algorithm.Online)
    (input : Instance Page) (request : Request Page)
    (hlast : ∀ other ∈ input.requests, other.arrival ≤ request.arrival) {t : Time}
    (ht : t ≤ request.arrival) :
    (algorithm (input.appendRequest request hlast)).cacheBefore t =
      (algorithm input).cacheBefore t := by
  apply online.cacheBefore_eq _ _ (by rfl)
  intro s hs
  exact input.appendRequest_upTo request hlast (hs.trans_le ht)

/-- **One release.**  Every miss of the run so far is still a miss of the
extended run, and the new request is a miss as well. -/
theorem appendRequest_misses {algorithm : Algorithm Page} (online : algorithm.Online)
    (input : Instance Page) (request : Request Page)
    (hearlier : ∀ other ∈ input.requests, other.arrival ≤ request.arrival)
    (hold : ∀ other ∈ input.requests,
      other.page ∉ (algorithm input).cacheBefore other.arrival)
    (hnew : request.page ∉ (algorithm input).cacheBefore request.arrival) :
    ∀ other ∈ (input.appendRequest request hearlier).requests,
      other.page ∉
        (algorithm (input.appendRequest request hearlier)).cacheBefore other.arrival := by
  intro other hother
  rcases List.mem_append.mp hother with hother | hother
  · rw [appendRequest_cacheBefore_le online input request hearlier
      (hearlier other hother)]
    exact hold other hother
  · rw [List.mem_singleton.mp hother,
      appendRequest_cacheBefore_le online input request hearlier le_rfl]
    exact hnew

end
end PagingWithDelay.DeadlineLowerBound
