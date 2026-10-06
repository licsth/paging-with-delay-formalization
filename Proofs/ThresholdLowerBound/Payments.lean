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
      have hsplit (q : β) : (((a :: rest).filter fun b => key b = q).map f).sum =
          (if key a = q then f a else 0) + ((rest.filter fun b => key b = q).map f).sum := by
        by_cases h : key a = q <;> simp [h]
      have hcount : (K.map fun q => if key a = q then f a else 0).sum ≤ f a := by
        rw [List.sum_map_eq_nsmul_single (key a) _ fun q hq _ => if_neg (Ne.symm hq), if_pos rfl]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (List.nodup_iff_count_le_one.mp hK (key a))
          with h | h <;> simp [h]
      simp only [hsplit, List.sum_map_add, List.map_cons, List.sum_cons]
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
  have hpay : ∀ e ∈ S.events,
      ((input.requests.filter fun r' => r'.page = e.fetched ∧
        S.serviceTime r' = some e.time).map S.requestCost).sum = δ :=
    algorithm.payment input
  -- every request is served by a fetch of its page inside its window
  set charge : Request Page → Time := fun r => (S.serviceTime r).getD 0 with hcharge
  have hevent : ∀ r ∈ input.requests, ∃ e ∈ S.events, e.time = charge r ∧
      e.fetched = r.page ∧ r.arrival ≤ e.time ∧ e.time ≤ r.arrival + window r := by
    intro r hr
    obtain ⟨e, he, hpage, harr, hserv⟩ := S.exists_fetch_of_miss r
      ((algorithm.feasible input).eventuallyServed r hr) (hmiss r hr)
    refine ⟨e, he, by simp only [hcharge, hserv, Option.getD_some], hpage, harr,
      le_of_not_gt fun hlt => ?_⟩
    -- otherwise the request alone would cost more than its payment `δ`
    have hle : S.requestCost r ≤ δ := by
      rw [← hpay e he]
      exact List.le_sum_of_mem (List.mem_map_of_mem (by simp [hr, hpage, hserv]))
    refine hle.not_gt ?_
    simp only [Schedule.requestCost, Schedule.serviceDelay, hserv, Option.getD_some]
    exact hlate r hr _ (lt_tsub_iff_left.mpr hlt)
  -- separated requests are charged to distinct `(time, page)` pairs
  have hdistinct : input.requests.Pairwise fun first second =>
      (charge first, first.page) ≠ (charge second, second.page) := by
    refine hsep.imp_of_mem fun hfirst hsecond hcase hpair => ?_
    rcases hcase with hpages | hwindows
    · exact hpages (Prod.mk.inj hpair).2
    · obtain ⟨e₁, -, ht₁, -, -, hwin₁⟩ := hevent _ hfirst
      obtain ⟨e₂, -, ht₂, -, harr₂, -⟩ := hevent _ hsecond
      have : e₁.time < e₂.time := (hwin₁.trans_lt hwindows).trans_le harr₂
      rw [ht₁, ht₂, (Prod.mk.inj hpair).1] at this
      exact lt_irrefl _ this
  -- fetches
  have hfetch : input.requests.length ≤ S.fetchCount :=
    DeadlineLowerBound.length_le_fetchCount S input.requests charge
      (fun r hr => by
        obtain ⟨e, he, ht, hp, -⟩ := hevent r hr
        exact ⟨e, he, ht, hp⟩) hdistinct
  -- payments
  set key : Request Page → Option Time × Page := fun r => (S.serviceTime r, r.page) with hkey
  set K := input.requests.map fun r => ((some (charge r) : Option Time), r.page) with hK
  have hKnodup : K.Nodup :=
    List.pairwise_map.mpr (hdistinct.imp fun hne heq => hne (by
      simp only [Prod.mk.injEq, Option.some.injEq] at heq ⊢; exact heq))
  have hfiber : ∀ q ∈ K,
      ((input.requests.filter fun r => key r = q).map S.requestCost).sum = δ := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    obtain ⟨e, he, ht, hp, -, -⟩ := hevent r hr
    rw [← hpay e he]
    congr 2
    apply List.filter_congr
    intro r' _
    simp only [hkey, Prod.mk.injEq, ← ht, ← hp]
    rw [Bool.eq_iff_iff]
    simp [and_comm]
  have hdelay : (input.requests.length : Cost) * δ ≤ S.totalDelay input := by
    have h := sum_fibers_le input.requests S.requestCost key K hKnodup
    rwa [List.map_congr_left hfiber, List.map_const', List.sum_replicate, hK,
      List.length_map, nsmul_eq_mul] at h
  calc (1 + δ) * (input.requests.length : Cost)
      = input.requests.length + input.requests.length * δ := by ring
    _ ≤ S.fetchCount + S.totalDelay input := add_le_add (by exact_mod_cast hfetch) hdelay

end ThresholdLowerBound

end
end PagingWithDelay
