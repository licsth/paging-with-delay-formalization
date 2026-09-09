import PagingWithDelay.Competitive.Core

/-!
# Comparator occupancy at residency ticks

The public `cacheBefore` convention excludes comparator events stamped at the
queried time.  The charging argument instead needs the cache after all such
events; this auxiliary view makes that distinction explicit.
-/

namespace PagingWithDelay.Competitive

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- Comparator cache after every event whose timestamp is at most `t`. -/
def comparatorCacheAt (schedule : Schedule Page) (t : Time) : Finset Page :=
  schedule.events.foldl
    (fun current event => if event.time ≤ t then event.cacheAfter else current) ∅

private theorem foldl_cache_card_le
    (t : Time) (events : List (FetchEvent Page)) (initial : Finset Page)
    (bound : ℕ) (hinitial : initial.card ≤ bound)
    (hevents : ∀ event ∈ events, event.cacheAfter.card ≤ bound) :
    (events.foldl
      (fun current event => if event.time ≤ t then event.cacheAfter else current)
      initial).card ≤ bound := by
  induction events generalizing initial with
  | nil => simpa using hinitial
  | cons event rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · by_cases htime : event.time ≤ t
        · simpa [htime] using hevents event (by simp)
        · simpa [htime] using hinitial
      · intro later hlater
        exact hevents later (by simp [hlater])

/-- Feasibility bounds comparator occupancy at every real time, including
times shared by several comparator events. -/
theorem comparatorCacheAt_card_le (schedule : Schedule Page)
    (input : Instance Page) (feasible : schedule.Feasible input) (t : Time) :
    (comparatorCacheAt schedule t).card ≤ input.cacheSize := by
  unfold comparatorCacheAt
  apply foldl_cache_card_le t schedule.events ∅ input.cacheSize
  · simp
  · exact feasible.capacity

/-- The occupancy bound specialized to a FIFO payment time. -/
theorem comparatorCacheAt_paymentTime_card_le (input : Instance Page)
    (comparator : Schedule Page) (feasible : comparator.Feasible input)
    (i : PaymentIndex input) :
    (comparatorCacheAt comparator (paymentTime input i)).card ≤ input.cacheSize :=
  comparatorCacheAt_card_le comparator input feasible _

private theorem fetched_mem_cacheAfter_of_validTransitions
    {previous : Finset Page} {events : List (FetchEvent Page)}
    (hvalid : Schedule.ValidTransitionsFrom previous events)
    {event : FetchEvent Page} (hevent : event ∈ events) :
    event.fetched ∈ event.cacheAfter := by
  induction events generalizing previous with
  | nil => simp at hevent
  | cons head tail ih =>
      simp only [Schedule.ValidTransitionsFrom] at hvalid
      rcases hvalid with ⟨hhead, _, htail⟩
      rcases List.mem_cons.mp hevent with rfl | hevent
      · exact hhead
      · exact ih htail hevent

private theorem firstEvictionAfter_le_of_absent
    (schedule : Schedule Page) (feasible : schedule.Feasible input)
    (i : Fin schedule.events.length) {j : ℕ}
    (hij : (i : ℕ) < j) (hj : j < schedule.events.length)
    (habsent : (schedule.events.get i).fetched ∉ schedule.events[j].cacheAfter) :
    ∃ eviction,
      firstEvictionAfter schedule i = some eviction ∧
      eviction ≤ schedule.events[j].time := by
  let predicate : ℕ → Bool := fun n =>
    decide ((i : ℕ) < n ∧ (schedule.events[n]?).any (fun later =>
      decide ((schedule.events.get i).fetched ∉ later.cacheAfter)) = true)
  have hpj : predicate j = true := by
    simp [predicate, hij, List.getElem?_eq_getElem hj]
    exact habsent
  have hjmem : j ∈ List.range schedule.events.length := by simp [hj]
  cases hfind : (List.range schedule.events.length).find? predicate with
  | none =>
      exact ((List.find?_eq_none.mp hfind j hjmem) hpj).elim
  | some evictionIndex =>
      have hspec := List.find?_some hfind
      have heventIndex : evictionIndex < schedule.events.length := by
        have : evictionIndex ∈ List.range schedule.events.length :=
          List.mem_of_find?_eq_some hfind
        simpa using this
      have hminimal : evictionIndex ≤ j := by
        obtain ⟨_, position, hposition, heq, hbefore⟩ :=
          List.find?_eq_some_iff_getElem.mp hfind
        have hpositionEq : position = evictionIndex := by
          simpa using heq
        subst position
        by_contra hnot
        have hjlt : j < evictionIndex := Nat.lt_of_not_ge hnot
        have hfalse := hbefore j hjlt
        simp [hpj] at hfalse
      have htime : schedule.events[evictionIndex].time ≤ schedule.events[j].time := by
        rcases hminimal.eq_or_lt with rfl | hlt
        · exact le_rfl
        · exact List.pairwise_iff_get.mp feasible.chronological
            ⟨evictionIndex, heventIndex⟩ ⟨j, hj⟩ hlt
      refine ⟨schedule.events[evictionIndex].time, ?_, htime⟩
      unfold firstEvictionAfter
      change ((List.range schedule.events.length).find? predicate).bind
        (fun n => (schedule.events[n]?).map FetchEvent.time) = some _
      rw [hfind]
      simp [List.getElem?_eq_getElem heventIndex]

private theorem foldl_preserves_page
    (page : Page) (t : Time) (events : List (FetchEvent Page))
    (initial : Finset Page) (hinitial : page ∈ initial)
    (hall : ∀ event ∈ events, event.time ≤ t → page ∈ event.cacheAfter) :
    page ∈ events.foldl
      (fun current event => if event.time ≤ t then event.cacheAfter else current) initial := by
  induction events generalizing initial with
  | nil => simpa using hinitial
  | cons event rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · by_cases htime : event.time ≤ t
        · simpa [htime] using hall event (by simp) htime
        · simpa [htime] using hinitial
      · intro later hlater
        exact hall later (by simp [hlater])

/-- A comparator residency covering `t` occupies a slot after all comparator
events stamped `t`.  This is the same-time-safe form of the paper's residency
claim; `cacheBefore` cannot be used at the interval's closed starting point. -/
theorem mem_comparatorCacheAt_of_mem_residencies_contains
    (schedule : Schedule Page) (feasible : schedule.Feasible input)
    (interval : ResidencyInterval (Page := Page))
    (hinterval : interval ∈ residencies schedule) {t : Time}
    (hcontains : interval.Contains t) :
    interval.page ∈ comparatorCacheAt schedule t := by
  obtain ⟨index, hget⟩ := List.mem_iff_get.mp hinterval
  let i : Fin schedule.events.length := ⟨index, by simpa [residencies] using index.isLt⟩
  have hres : residencyAt schedule i = interval := by
    simpa [residencies, i] using hget
  rw [← hres] at hcontains ⊢
  let fetched := schedule.events.get i
  have hstart : fetched.time ≤ t := by simpa [residencyAt, fetched] using hcontains.1
  have hfetched : fetched.fetched ∈ fetched.cacheAfter := by
    apply fetched_mem_cacheAfter_of_validTransitions feasible.validTransitions
    exact List.get_mem schedule.events i
  have hsplit : schedule.events = schedule.events.take i ++
      fetched :: schedule.events.drop (i + 1) := by
    calc
      schedule.events = schedule.events.take (i + 1) ++
          schedule.events.drop (i + 1) := (List.take_append_drop _ _).symm
      _ = schedule.events.take i ++ schedule.events.get i ::
          schedule.events.drop (i + 1) := by
        rw [← List.take_concat_get i.isLt]
        exact List.concat_append
  unfold comparatorCacheAt
  rw [hsplit, List.foldl_append, List.foldl_cons]
  simp only [if_pos hstart]
  change fetched.fetched ∈ _
  apply foldl_preserves_page fetched.fetched t _ fetched.cacheAfter hfetched
  intro later hlater hlaterTime
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hlater
  let j : ℕ := (i : ℕ) + 1 + k
  have hjlt : j < schedule.events.length := by
    dsimp [j]
    have hklt : (k : ℕ) < schedule.events.length - ((i : ℕ) + 1) := by
      simpa using k.isLt
    omega
  have hj : schedule.events[j] = later := by
    have hopt : (schedule.events.drop ((i : ℕ) + 1))[k]? = some later := by
      calc
        _ = some ((schedule.events.drop ((i : ℕ) + 1))[(k : ℕ)]'k.isLt) :=
          List.getElem?_eq_getElem k.isLt
        _ = some later := by simpa using congrArg some hk
    have hglobal : schedule.events[j]? = some later := by
      dsimp [j]
      rw [← List.getElem?_drop]
      exact hopt
    simpa [List.getElem?_eq_getElem hjlt] using hglobal
  have hjgt : (i : ℕ) < j := by dsimp [j]; omega
  by_contra habsent
  obtain ⟨eviction, heviction, hle⟩ :=
    firstEvictionAfter_le_of_absent schedule feasible i hjgt hjlt (by simpa [hj] using habsent)
  have he_lt_t : t < eviction := by
    simpa [ResidencyInterval.Contains, residencyAt, heviction] using hcontains.2
  have hle' : eviction ≤ later.time := by simpa [hj] using hle
  exact (not_lt_of_ge (hle'.trans hlaterTime)) he_lt_t

/-- Direct form used by the class-C charging argument at a FIFO payment tick. -/
theorem mem_comparatorCacheAt_paymentTime_of_residency
    (input : Instance Page) (comparator : Schedule Page)
    (feasible : comparator.Feasible input) (i : PaymentIndex input)
    (interval : ResidencyInterval (Page := Page))
    (hinterval : interval ∈ residencies comparator)
    (hcontains : interval.Contains (paymentTime input i)) :
    interval.page ∈ comparatorCacheAt comparator (paymentTime input i) :=
  mem_comparatorCacheAt_of_mem_residencies_contains comparator feasible interval
    hinterval hcontains

/-! The converse direction at the strict `cacheBefore` convention.  These
lemmas deliberately derive residency provenance from the transition trace;
it is not part of schedule feasibility by definition. -/

private theorem validTransitions_get_transition
    {previous : Finset Page} {events : List (FetchEvent Page)}
    (hvalid : Schedule.ValidTransitionsFrom previous events)
    (j : Fin events.length) :
    let before := if (j : ℕ) = 0 then previous
      else (events[(j : ℕ) - 1]'(by omega)).cacheAfter
    (events.get j).fetched ∈ (events.get j).cacheAfter ∧
      (events.get j).cacheAfter \ before = {(events.get j).fetched} := by
  induction events generalizing previous with
  | nil => exact Fin.elim0 j
  | cons head tail ih =>
      simp only [Schedule.ValidTransitionsFrom] at hvalid
      rcases hvalid with ⟨hfetch, hdiff, htail⟩
      refine Fin.cases ?_ (fun q => ?_) j
      · simpa using ⟨hfetch, hdiff⟩
      · rcases q with ⟨q, hq⟩
        cases q with
        | zero => simpa using ih htail (⟨0, hq⟩ : Fin tail.length)
        | succ n => simpa using ih htail (⟨n + 1, hq⟩ : Fin tail.length)

private theorem cacheAfter_provenance
    (schedule : Schedule Page) (feasible : schedule.Feasible input)
    (j : Fin schedule.events.length) {page : Page}
    (hpage : page ∈ (schedule.events.get j).cacheAfter) :
    ∃ i : Fin schedule.events.length,
      (i : ℕ) ≤ j ∧ (schedule.events.get i).fetched = page ∧
      ∀ l : Fin schedule.events.length, (i : ℕ) ≤ l → (l : ℕ) ≤ j →
        page ∈ (schedule.events.get l).cacheAfter := by
  induction hj : (j : ℕ) using Nat.strong_induction_on generalizing j with
  | h n ih =>
    by_cases hn : n = 0
    · have hjzero : (j : ℕ) = 0 := by omega
      have ht := validTransitions_get_transition feasible.validTransitions j
      have hdiff : (schedule.events.get j).cacheAfter \ (∅ : Finset Page) =
          {(schedule.events.get j).fetched} := by
        simpa [hjzero] using ht.2
      have hnew : page ∈ (schedule.events.get j).cacheAfter \ (∅ : Finset Page) := by
        simpa using hpage
      have : page = (schedule.events.get j).fetched := by
        rw [hdiff] at hnew
        simpa using hnew
      refine ⟨j, by omega, this.symm, ?_⟩
      intro l _ hlj
      have : l = j := Fin.eq_of_val_eq (by omega)
      simpa [this] using hpage
    · let pred : Fin schedule.events.length := ⟨n - 1, by omega⟩
      have hjpred : (pred : ℕ) < n := by dsimp [pred]; omega
      have ht := validTransitions_get_transition feasible.validTransitions j
      by_cases hfetch : (schedule.events.get j).fetched = page
      · refine ⟨j, by omega, hfetch, ?_⟩
        intro l _ hlj
        have : l = j := Fin.eq_of_val_eq (by omega)
        simpa [this] using hpage
      · have hprev : page ∈ (schedule.events.get pred).cacheAfter := by
          by_contra habsent
          have hnew : page ∈ (schedule.events.get j).cacheAfter \
              (schedule.events.get pred).cacheAfter := Finset.mem_sdiff.mpr ⟨hpage, habsent⟩
          have hzero : (j : ℕ) ≠ 0 := by omega
          have hdiff : (schedule.events.get j).cacheAfter \
              (schedule.events.get pred).cacheAfter = {(schedule.events.get j).fetched} := by
            simpa [hn, pred, hj] using ht.2
          rw [hdiff] at hnew
          have heq : page = (schedule.events.get j).fetched := by simpa using hnew
          exact hfetch heq.symm
        obtain ⟨i, hij, hifetch, hall⟩ := ih (n - 1) hjpred pred hprev rfl
        refine ⟨i, hij.trans (by omega), hifetch, ?_⟩
        · intro l hil hlj
          by_cases hl : (l : ℕ) = (j : ℕ)
          · simpa [Fin.eq_of_val_eq hl] using hpage
          · have hlj' : (l : ℕ) ≤ pred := by dsimp [pred]; omega
            exact hall l hil hlj'

private theorem foldl_last_before (events : List (FetchEvent Page))
    (initial : Finset Page) (t : Time) :
    (events.foldl
      (fun current event => if event.time < t then event.cacheAfter else current)
      initial = initial ∧ ∀ event ∈ events, ¬ event.time < t) ∨
    ∃ j : Fin events.length,
      events.foldl
        (fun current event => if event.time < t then event.cacheAfter else current)
        initial = (events.get j).cacheAfter ∧
      (events.get j).time < t ∧
      ∀ l : Fin events.length, (j : ℕ) < l → ¬ (events.get l).time < t := by
  induction events generalizing initial with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rcases ih (if head.time < t then head.cacheAfter else initial) with hnone | hlast
      · rcases hnone with ⟨heq, hnone⟩
        by_cases hhead : head.time < t
        · right
          refine ⟨⟨0, by simp⟩, ?_, hhead, ?_⟩
          · simpa [hhead] using heq
          · intro l hl
            rcases l with ⟨l, hlen⟩
            cases l with
            | zero =>
                change 0 < 0 at hl
                omega
            | succ n =>
                have hn : n < tail.length := by simpa using hlen
                exact hnone tail[n] (List.getElem_mem hn)
        · left
          refine ⟨by simpa [hhead] using heq, ?_⟩
          intro event hevent
          rcases List.mem_cons.mp hevent with rfl | hevent
          · exact hhead
          · exact hnone event hevent
      · obtain ⟨j, heq, hjtime, hafter⟩ := hlast
        right
        refine ⟨j.succ, ?_, by simpa using hjtime, ?_⟩
        · simpa using heq
        · intro l hl
          rcases l with ⟨l, hlen⟩
          cases l with
          | zero =>
              change (j : ℕ) + 1 < 0 at hl
              omega
          | succ n =>
              have hn : n < tail.length := by simpa using hlen
              change (j : ℕ) + 1 < n + 1 at hl
              apply hafter ⟨n, hn⟩
              exact Nat.lt_of_succ_lt_succ hl

private theorem firstEvictionAfter_some_index
    (schedule : Schedule Page) (i : Fin schedule.events.length) {finish : Time}
    (hfinish : firstEvictionAfter schedule i = some finish) :
    ∃ j : Fin schedule.events.length, (i : ℕ) < j ∧
      (schedule.events.get i).fetched ∉ (schedule.events.get j).cacheAfter ∧
      (schedule.events.get j).time = finish := by
  unfold firstEvictionAfter at hfinish
  dsimp only at hfinish
  generalize hfind : (List.range schedule.events.length).find? (fun j =>
      (i : ℕ) < j ∧ (schedule.events[j]?).any fun later =>
        (schedule.events.get i).fetched ∉ later.cacheAfter) = found at hfinish
  cases found with
  | none =>
      exact nomatch hfinish
  | some j =>
      have hjmem := List.mem_of_find?_eq_some hfind
      have hjlt : j < schedule.events.length := by simpa using hjmem
      have hpred := List.find?_some hfind
      simp only [List.getElem?_eq_getElem hjlt, Option.any_some,
        decide_eq_true_eq] at hpred
      simp only [Option.bind_some] at hfinish
      rw [List.getElem?_eq_getElem hjlt] at hfinish
      refine ⟨⟨j, hjlt⟩, hpred.1, hpred.2, ?_⟩
      change schedule.events[j].time = finish
      exact Option.some.inj hfinish

/-- Every page visible immediately before `t` is backed by an actual maximal
residency interval containing that pre-event instant. -/
theorem residency_of_mem_cacheBefore (schedule : Schedule Page)
    (feasible : schedule.Feasible input) {page : Page} {t : Time}
    (hpage : page ∈ schedule.cacheBefore t) :
    ∃ interval ∈ residencies schedule,
      interval.page = page ∧ interval.ContainsBefore t := by
  have hlast := foldl_last_before schedule.events (∅ : Finset Page) t
  unfold Schedule.cacheBefore at hpage
  rcases hlast with hnone | ⟨j, hfold, hjtime, hafter⟩
  · rw [hnone.1] at hpage
    simp at hpage
  · rw [hfold] at hpage
    obtain ⟨i, hij, hfetch, hall⟩ := cacheAfter_provenance schedule feasible j hpage
    let interval := residencyAt schedule i
    refine ⟨interval, ?_, ?_, ?_⟩
    · simp [interval, residencies]
    · simpa [interval, residencyAt] using hfetch
    · constructor
      · have htime : (schedule.events.get i).time ≤
            (schedule.events.get j).time := by
          rcases hij.eq_or_lt with heq | hlt
          · simp [Fin.eq_of_val_eq heq]
          · exact List.pairwise_iff_get.mp feasible.chronological i j hlt
        simpa [interval, residencyAt] using htime.trans_lt hjtime
      · cases hf : firstEvictionAfter schedule i with
        | none =>
            change (firstEvictionAfter schedule i).elim True (fun finish => t ≤ finish)
            rw [hf]
            trivial
        | some finish =>
            simp only [interval, residencyAt, hf,
              Option.elim_some]
            by_contra hnot
            have hfinlt : finish < t := lt_of_not_ge hnot
            obtain ⟨l, hil, habsent, hltime⟩ :=
              firstEvictionAfter_some_index schedule i hf
            by_cases hlj : (l : ℕ) ≤ j
            · rw [hfetch] at habsent
              exact habsent (hall l (Nat.le_of_lt hil) hlj)
            · have hjl : (j : ℕ) < l := Nat.lt_of_not_ge hlj
              exact hafter l hjl (by rw [hltime]; exact hfinlt)

end
end PagingWithDelay.Competitive
