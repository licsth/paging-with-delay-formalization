import Proofs.DeadlineLowerBound.Online

/-!
# Every separated miss costs a threshold algorithm `1 + δ`

A threshold algorithm with threshold `δ` never charges a single request more
than `δ`: the request is one summand of the payment of the fetch that serves
it.  So if a request's curve exceeds `δ` after its window, the request is
served by a fetch inside the window.  Separated requests are served by
fetches at distinct `(time, page)` pairs, and each such pair is a fetch
together with a payment of `δ`.
-/

namespace PagingWithDelay

open Finset

noncomputable section

variable {Page : Type*} [DecidableEq Page]

namespace ThresholdLowerBound

/-- Summing over distinct keys the requests carrying each key counts each
request at most once. -/
theorem sum_fibers_le {α β : Type*} [DecidableEq β] (L : List α) (f : α → Cost)
    (key : α → β) (K : List β) (hK : K.Nodup) :
    (K.map fun q => ((L.filter fun a => key a = q).map f).sum).sum ≤ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a rest ih =>
      have hsplit : (K.map fun q => (((a :: rest).filter fun b => key b = q).map f).sum).sum =
          (K.map fun q => if key a = q then f a else 0).sum +
            (K.map fun q => ((rest.filter fun b => key b = q).map f).sum).sum := by
        rw [← List.sum_map_add]
        congr 1
        apply List.map_congr_left
        intro q _
        by_cases h : key a = q <;> simp [h]
      have hzero : ∀ u : List β, key a ∉ u →
          (u.map fun q => if key a = q then f a else 0).sum = 0 := by
        intro u hu
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        have hne : key a ≠ q := fun h => hu (h ▸ hq)
        rw [if_neg hne]
      have hcount : (K.map fun q => if key a = q then f a else 0).sum ≤ f a := by
        by_cases hmem : key a ∈ K
        · obtain ⟨s, t, rfl⟩ := List.append_of_mem hmem
          have hnd := (List.nodup_middle.mp hK |> List.nodup_cons.mp).1
          have hs : key a ∉ s := fun h => hnd (List.mem_append_left _ h)
          have ht : key a ∉ t := fun h => hnd (List.mem_append_right _ h)
          simp [List.map_append, hzero s hs, hzero t ht]
        · rw [hzero K hmem]
          exact zero_le _
      rw [hsplit, List.map_cons, List.sum_cons]
      exact add_le_add hcount ih

/-- **Each separated miss costs `1 + δ`.**  If every request of `input` is a
miss on arrival, its curve exceeds the threshold strictly after its window,
and any two requests ask for different pages or have disjoint windows, then a
threshold algorithm pays at least `1 + δ` per request. -/
theorem cost_ge (algorithm : ThresholdAlgorithm Page) (input : Instance Page)
    (window : Request Page → Time)
    (hmiss : ∀ request ∈ input.requests,
      request.page ∉ (algorithm.run input).cacheBefore request.arrival)
    (hlate : ∀ request ∈ input.requests, ∀ wait, window request < wait →
      algorithm.threshold input.cacheSize < request.delay wait)
    (hsep : input.requests.Pairwise fun first second =>
      first.page ≠ second.page ∨ first.arrival + window first < second.arrival) :
    (1 + algorithm.threshold input.cacheSize) * input.requests.length ≤
      (algorithm.run input).totalCost input := by
  classical
  set S := algorithm.run input with hS
  set δ := algorithm.threshold input.cacheSize with hδ
  have feasible : S.Feasible input := algorithm.feasible input
  -- every request is served by a fetch of its page inside its window
  have hpay : ∀ e ∈ S.events,
      ((input.requests.filter fun r' => r'.page = e.fetched ∧
        S.serviceTime r' = some e.time).map S.requestCost).sum = δ :=
    algorithm.payment input
  have hevent : ∀ r ∈ input.requests, ∃ e ∈ S.events, e.fetched = r.page ∧
      r.arrival ≤ e.time ∧ e.time ≤ r.arrival + window r ∧ S.serviceTime r = some e.time := by
    intro r hr
    obtain ⟨e, he, hpage, harr, hserv⟩ :=
      S.exists_fetch_of_miss r (feasible.eventuallyServed r hr) (hmiss r hr)
    refine ⟨e, he, hpage, harr, ?_, hserv⟩
    by_contra hlt
    have hcost : S.requestCost r = r.delay (e.time - r.arrival) := by
      simp only [Schedule.requestCost, Schedule.serviceDelay, hserv, Option.getD_some]
    have hgt : δ < S.requestCost r := by
      rw [hcost]
      exact hlate r hr _ (by rw [lt_tsub_iff_left]; exact lt_of_not_ge hlt)
    have hmemf : r ∈ input.requests.filter
        (fun r' => r'.page = e.fetched ∧ S.serviceTime r' = some e.time) := by
      simp [hr, hpage, hserv]
    have hle : S.requestCost r ≤ δ := by
      rw [← hpay e he]
      exact List.le_sum_of_mem (List.mem_map_of_mem hmemf)
    exact absurd hle (not_le.mpr hgt)
  set charge : Request Page → Time := fun r => (S.serviceTime r).getD 0 with hcharge
  have hchargeEvent : ∀ r ∈ input.requests, ∃ e ∈ S.events, e.time = charge r ∧
      e.fetched = r.page ∧ r.arrival ≤ e.time ∧ e.time ≤ r.arrival + window r ∧
      S.serviceTime r = some (charge r) := by
    intro r hr
    obtain ⟨e, he, hpage, harr, hwin, hserv⟩ := hevent r hr
    have : charge r = e.time := by
      show (S.serviceTime r).getD 0 = e.time
      rw [hserv]
      rfl
    exact ⟨e, he, this.symm, hpage, harr, hwin, by rw [hserv, this]⟩
  -- separated requests are charged to distinct `(time, page)` pairs
  have hdistinct : input.requests.Pairwise fun first second =>
      (charge first, first.page) ≠ (charge second, second.page) := by
    refine hsep.imp_of_mem ?_
    intro first second hfirst hsecond hcase hpair
    rcases hcase with hpages | hwindows
    · exact hpages (congrArg Prod.snd hpair)
    · obtain ⟨e₁, -, ht₁, -, -, hwin₁, -⟩ := hchargeEvent first hfirst
      obtain ⟨e₂, -, ht₂, -, harr₂, -, -⟩ := hchargeEvent second hsecond
      have htimes : charge first = charge second := congrArg Prod.fst hpair
      have : charge second < charge second :=
        calc charge second = charge first := htimes.symm
          _ ≤ first.arrival + window first := ht₁ ▸ hwin₁
          _ < second.arrival := hwindows
          _ ≤ charge second := ht₂ ▸ harr₂
      exact lt_irrefl _ this
  -- fetches
  have hfetch : input.requests.length ≤ S.fetchCount :=
    DeadlineLowerBound.length_le_fetchCount S input.requests charge
      (fun r hr => by
        obtain ⟨e, he, ht, hp, -⟩ := hchargeEvent r hr
        exact ⟨e, he, ht, hp⟩) hdistinct
  -- payments
  set key : Request Page → Option Time × Page := fun r => (S.serviceTime r, r.page) with hkey
  set K := input.requests.map fun r => ((some (charge r) : Option Time), r.page) with hK
  have hKnodup : K.Nodup := by
    refine List.pairwise_map.mpr (hdistinct.imp ?_)
    intro first second hne heq
    apply hne
    simp only [Prod.mk.injEq, Option.some.injEq] at heq ⊢
    exact heq
  have hfiber : ∀ q ∈ K,
      ((input.requests.filter fun r => key r = q).map S.requestCost).sum = δ := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    obtain ⟨e, he, ht, hp, -, -, -⟩ := hchargeEvent r hr
    rw [← hpay e he]
    congr 2
    apply List.filter_congr
    intro r' _
    simp only [hkey, Prod.mk.injEq, ← ht, ← hp]
    rw [Bool.eq_iff_iff]
    simp [and_comm]
  have hdelay : (input.requests.length : Cost) * δ ≤ S.totalDelay input := by
    have h := sum_fibers_le input.requests S.requestCost key K hKnodup
    rw [List.map_congr_left hfiber, List.map_const', List.sum_replicate, hK,
      List.length_map, nsmul_eq_mul] at h
    exact h
  calc (1 + δ) * (input.requests.length : Cost)
      = input.requests.length + input.requests.length * δ := by ring
    _ ≤ S.fetchCount + S.totalDelay input := add_le_add (by exact_mod_cast hfetch) hdelay
    _ = S.totalCost input := rfl

end ThresholdLowerBound

end
end PagingWithDelay
