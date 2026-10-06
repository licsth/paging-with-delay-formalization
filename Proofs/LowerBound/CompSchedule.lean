import Proofs.LowerBound.Steps
import Proofs.EventLoop.ServiceBridge

/-!
# The comparator's schedule

The offline solution of the TeX proof, written out.  It starts from the common
initial cache `{b, v₁ … v_{k-1}}`, never gives up `v₁ … v_{k-1}`, and besides
them holds one of `b`, `c` at a time: it first fetches `c` (evicting `b`) and,
once per run, moves to the other one at the moment the request there is
issued.  Runs alternate the roles of `b` and `c`, so the fetch of run `r` puts
the comparator on the page run `r + 1` starts on.  Finally it fetches `a`,
which serves the one request per run it has left pending.

Its whole history is therefore the list

```text
c = swapBC 0 2,  swapBC 1 2, …, swapBC runs 2,  a
```

of `runs + 2` fetches, and the first `runs + 1` are `phaseEvent`s: they are
what makes the comparator's cache between two of them a single closed form,
`heldCache k pages (swapBC r 2)`.
-/

namespace PagingWithDelay.LowerBound

open PagingWithDelay

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-! ## The cache contents -/

/-- Codes of the `k - 1` pages the comparator never gives up. -/
def vCodes (k : ℕ) : List ℕ := List.range' 3 (k - 1)

theorem mem_vCodes_iff (k c : ℕ) : c ∈ vCodes k ↔ 3 ≤ c ∧ c < 3 + (k - 1) := by
  simp [vCodes, List.mem_range'_1]

theorem vCodes_lt (k : ℕ) (hk : 0 < k) {c : ℕ} (h : c ∈ vCodes k) : c < k + 2 := by
  rw [mem_vCodes_iff] at h; omega

/-- The pages the comparator never gives up. -/
def vSet (k : ℕ) (pages : Fin (k + 2) ↪ Page) : Finset Page :=
  ((vCodes k).map (page k pages)).toFinset

/-- The comparator's cache while it holds the page with code `c`. -/
def heldCache (k : ℕ) (pages : Fin (k + 2) ↪ Page) (c : ℕ) : Finset Page :=
  insert (page k pages c) (vSet k pages)

theorem mem_vSet_iff {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) {c : ℕ}
    (hc : c < k + 2) : page k pages c ∈ vSet k pages ↔ c ∈ vCodes k := by
  simp only [vSet, List.mem_toFinset, List.mem_map]
  refine ⟨fun ⟨d, hd, hpd⟩ => ?_, fun h => ⟨c, h, rfl⟩⟩
  rwa [page_injOn pages (vCodes_lt k hk hd) hc hpd] at hd

theorem vSet_card {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) :
    (vSet k pages).card = k - 1 := by
  rw [vSet, List.toFinset_card_of_nodup ((List.nodup_range' ..).map_on fun a ha b hb h =>
    page_injOn pages (vCodes_lt k hk ha) (vCodes_lt k hk hb) h)]
  simp [vCodes]

theorem heldCache_card {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) {c : ℕ}
    (hc : c < k + 2) (hnot : c ∉ vCodes k) : (heldCache k pages c).card = k := by
  rw [heldCache, Finset.card_insert_of_notMem (by rw [mem_vSet_iff hk pages hc]; exact hnot),
    vSet_card hk pages]
  omega

theorem vSet_subset_heldCache {k : ℕ} (pages : Fin (k + 2) ↪ Page) (c : ℕ) :
    vSet k pages ⊆ heldCache k pages c := Finset.subset_insert _ _

/-! ## Codes of the pages the comparator swaps -/

theorem swapBC_two_lt (k r : ℕ) (hk : 0 < k) : swapBC r 2 < k + 2 := by
  unfold swapBC; split_ifs <;> omega

theorem swapBC_two_notMem_vCodes (k r : ℕ) : swapBC r 2 ∉ vCodes k := by
  rw [mem_vCodes_iff]; unfold swapBC; split_ifs <;> omega

theorem swapBC_two_ne_succ (r : ℕ) : swapBC (r + 1) 2 ≠ swapBC r 2 := by
  unfold swapBC; split_ifs <;> omega

theorem swapBC_two_ne_zero (r : ℕ) : swapBC r 2 ≠ 0 := by
  unfold swapBC; split_ifs <;> omega

/-- The fetch of run `r` lands on the page run `r + 1` starts on. -/
theorem swapBC_one_eq (r : ℕ) : swapBC r 1 = swapBC (r + 1) 2 := by
  unfold swapBC; split_ifs <;> omega

theorem page_notMem_heldCache {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) {c d : ℕ}
    (hc : c < k + 2) (hd : d < k + 2) (hne : c ≠ d) (hnot : c ∉ vCodes k) :
    page k pages c ∉ heldCache k pages d := by
  rw [heldCache, Finset.mem_insert, mem_vSet_iff hk pages hc]
  rintro (h | h)
  · exact hne (page_injOn pages hc hd h)
  · exact hnot h

theorem page_zero_notMem_heldCache {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) (c : ℕ)
    (hc : c < k + 2) (hc0 : c ≠ 0) : page k pages 0 ∉ heldCache k pages c :=
  page_notMem_heldCache hk pages (by omega) hc hc0.symm (by simp [mem_vCodes_iff])

/-! ## The initial cache -/

/-- The common initial cache is `{b, v₁ … v_{k-1}}`: the comparator starts
holding `b` besides the pages it never gives up. -/
theorem initialCache_toFinset {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) :
    (initialCache k pages).toFinset = heldCache k pages 1 := by
  ext p
  simp only [initialCache, heldCache, vSet, List.mem_toFinset, List.mem_map,
    List.mem_range, Finset.mem_insert, mem_vCodes_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    by_cases h0 : n = 0
    · subst n; left; rfl
    · right
      exact ⟨k + 2 - n, by omega, by simp [initialCode, h0]⟩
  · rintro (rfl | ⟨c, hc, rfl⟩)
    · exact ⟨0, hk, by simp [initialCode]⟩
    · refine ⟨k + 2 - c, by omega, ?_⟩
      rw [initialCode, if_neg (by omega)]
      congr 1
      omega

/-! ## The events -/

/-- The time from which the comparator holds `swapBC r 2`: the moment the
request on that page is issued, at the end of run `r - 1`. -/
def phaseTime (k r : ℕ) : Time :=
  if r = 0 then 0 else arrivalTime k (runLength k * (r - 1) + (k + 2))

/-- The fetch that moves the comparator onto `swapBC r 2`.  Its `r = 0` case
is the initial fetch of `c`. -/
def phaseEvent (k : ℕ) (pages : Fin (k + 2) ↪ Page) (r : ℕ) : FetchEvent Page where
  time := phaseTime k r
  fetched := page k pages (swapBC r 2)
  cacheAfter := heldCache k pages (swapBC r 2)

/-- When the comparator finally fetches `a`: after every request has arrived,
and long before the delay curves leave their plateau. -/
def finalTime (k runs : ℕ) : Time := ((4 * (runLength k * runs) + 4 : ℕ) : Cost) / 4

def finalEvent (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) : FetchEvent Page where
  time := finalTime k runs
  fetched := page k pages 0
  cacheAfter := {page k pages 0}

def compEvents (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) : List (FetchEvent Page) :=
  (List.range' 0 (runs + 1)).map (phaseEvent k pages) ++ [finalEvent k runs pages]

/-- **The comparator.** -/
def comparator (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) : Schedule Page :=
  ⟨(initialCache k pages).toFinset, compEvents k runs pages⟩

/-! ## Feasibility -/

theorem insert_sdiff_of_subset {A B : Finset Page} {x : Page} (hAB : A ⊆ B) (hx : x ∉ B) :
    insert x A \ B = {x} := by
  rw [Finset.insert_sdiff_of_notMem _ hx, Finset.sdiff_eq_empty_iff_subset.mpr hAB]; rfl

/-- The cache the comparator is left in by a block of events. -/
def lastCache : Finset Page → List (FetchEvent Page) → Finset Page
  | prev, [] => prev
  | _, event :: rest => lastCache event.cacheAfter rest

theorem lastCache_concat : ∀ (A : List (FetchEvent Page)) (prev : Finset Page)
    (event : FetchEvent Page), lastCache prev (A ++ [event]) = event.cacheAfter
  | [], _, _ => rfl
  | e :: rest, _, event => lastCache_concat rest e.cacheAfter event

theorem validTransitionsFrom_append : ∀ (A : List (FetchEvent Page)) (prev : Finset Page)
    (B : List (FetchEvent Page)), Schedule.ValidTransitionsFrom prev A →
      Schedule.ValidTransitionsFrom (lastCache prev A) B →
      Schedule.ValidTransitionsFrom prev (A ++ B)
  | [], _, _, _, hB => hB
  | event :: rest, _, B, hA, hB =>
      ⟨hA.1, hA.2.1, validTransitionsFrom_append rest event.cacheAfter B hA.2.2 hB⟩

/-- The comparator moves from one of `b`, `c` to the other once per run. -/
theorem phaseBlock_valid {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) :
    ∀ n s (prev : Finset Page), vSet k pages ⊆ prev →
      page k pages (swapBC s 2) ∉ prev →
      Schedule.ValidTransitionsFrom prev ((List.range' s n).map (phaseEvent k pages)) := by
  intro n
  induction n with
  | zero => intro s prev _ _; trivial
  | succ n ih =>
      intro s prev hsub hnot
      refine ⟨Finset.mem_insert_self _ _, insert_sdiff_of_subset hsub hnot, ?_⟩
      exact ih (s + 1) (heldCache k pages (swapBC s 2)) (vSet_subset_heldCache pages _)
        (page_notMem_heldCache hk pages (swapBC_two_lt k (s + 1) hk)
          (swapBC_two_lt k s hk) (swapBC_two_ne_succ s) (swapBC_two_notMem_vCodes k (s + 1)))

theorem lastCache_phaseBlock {k : ℕ} (pages : Fin (k + 2) ↪ Page) (runs : ℕ)
    (prev : Finset Page) :
    lastCache prev ((List.range' 0 (runs + 1)).map (phaseEvent k pages)) =
      heldCache k pages (swapBC runs 2) := by
  rw [List.range'_concat]
  simp only [List.map_append, List.map_cons, List.map_nil, Nat.zero_add, Nat.one_mul]
  rw [lastCache_concat]
  rfl

theorem comparator_validTransitions {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page)
    (runs : ℕ) :
    Schedule.ValidTransitionsFrom (initialCache k pages).toFinset (compEvents k runs pages) := by
  rw [initialCache_toFinset hk pages]
  refine validTransitionsFrom_append _ _ _ ?_ ?_
  · exact phaseBlock_valid hk pages (runs + 1) 0 (heldCache k pages 1)
      (vSet_subset_heldCache pages 1)
      (page_notMem_heldCache hk pages (swapBC_two_lt k 0 hk) (by omega)
        (by unfold swapBC; simp) (swapBC_two_notMem_vCodes k 0))
  · rw [lastCache_phaseBlock pages runs]
    exact ⟨Finset.mem_singleton_self _, insert_sdiff_of_subset (Finset.empty_subset _)
      (page_zero_notMem_heldCache hk pages _ (swapBC_two_lt k runs hk) (swapBC_two_ne_zero runs)),
      trivial⟩

theorem comparator_capacity {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) (runs : ℕ) :
    ∀ event ∈ compEvents k runs pages, event.cacheAfter.card ≤ k := by
  intro event hevent
  simp only [compEvents, List.mem_append, List.mem_map, List.mem_singleton,
    List.mem_range'_1] at hevent
  rcases hevent with ⟨r, _, rfl⟩ | rfl
  · show (heldCache k pages (swapBC r 2)).card ≤ k
    rw [heldCache_card hk pages (swapBC_two_lt k r hk) (swapBC_two_notMem_vCodes k r)]
  · show ({page k pages 0} : Finset Page).card ≤ k
    simpa using hk

theorem comparator_fetchCount (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) :
    (comparator k runs pages).fetchCount = runs + 2 := by
  simp [comparator, Schedule.fetchCount, compEvents]

/-! ## Times -/

/-- The phase boundaries, in quarters. -/
def phaseQuarters (k r : ℕ) : ℕ :=
  if r = 0 then 0 else 4 * (runLength k * (r - 1) + (k + 2)) - 2

theorem phaseTime_eq (k r : ℕ) (hk : 0 < k) :
    phaseTime k r = ((phaseQuarters k r : Cost)) / 4 := by
  unfold phaseTime phaseQuarters
  split_ifs with h
  · simp
  · rw [arrivalTime_eq, arrivalQuarters_run k (r - 1) (k + 2) (by unfold runLength; omega),
      if_neg (by omega), if_pos rfl]

theorem phaseQuarters_mono (k : ℕ) {r r' : ℕ} (h : r ≤ r') :
    phaseQuarters k r ≤ phaseQuarters k r' := by
  unfold phaseQuarters
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact Nat.zero_le _
  · omega
  · have : runLength k * (r - 1) ≤ runLength k * (r' - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

theorem phaseQuarters_le_final {k : ℕ} (hk : 0 < k) {r runs : ℕ} (h : r ≤ runs) :
    phaseQuarters k r ≤ 4 * (runLength k * runs) + 4 := by
  have hL : runLength k = 2 * k + 2 := rfl
  unfold phaseQuarters
  split_ifs with h1
  · omega
  · have e : runLength k * (r - 1) + runLength k = runLength k * r := by
      rw [← Nat.mul_succ]; congr 1; omega
    have hmul : runLength k * r ≤ runLength k * runs := Nat.mul_le_mul_left _ h
    omega

theorem phaseTime_le_final {k : ℕ} (hk : 0 < k) {r runs : ℕ} (h : r ≤ runs) :
    phaseTime k r ≤ finalTime k runs := by
  rw [phaseTime_eq k r hk, finalTime]
  exact quarter_le (phaseQuarters_le_final hk h)

theorem comparator_chronological {k : ℕ} (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) (runs : ℕ) :
    (compEvents k runs pages).Pairwise (fun a b => a.time ≤ b.time) := by
  refine List.pairwise_append.mpr ⟨?_, List.pairwise_singleton _ _, ?_⟩
  · refine List.pairwise_map.mpr ((List.pairwise_lt_range' 1).imp fun {a b} hab => ?_)
    show phaseTime k a ≤ phaseTime k b
    rw [phaseTime_eq k a hk, phaseTime_eq k b hk]
    exact quarter_le (phaseQuarters_mono k hab.le)
  · intro a ha b hb
    simp only [List.mem_map, List.mem_range'_1, List.mem_singleton] at ha hb
    obtain ⟨r, _, rfl⟩ := ha
    exact hb ▸ phaseTime_le_final hk (by omega)

/-! ## The comparator's cache at a given time -/

theorem foldl_noop (t : Time) : ∀ (B : List (FetchEvent Page)) (x : Finset Page),
    (∀ e ∈ B, ¬ e.time < t) →
      B.foldl (fun cur e => if e.time < t then e.cacheAfter else cur) x = x := by
  intro B
  induction B with
  | nil => intro x _; rfl
  | cons e rest ih =>
      intro x h
      rw [List.foldl_cons, if_neg (h e (List.mem_cons_self ..))]
      exact ih x fun f hf => h f (List.mem_cons_of_mem e hf)

/-- The cache before `t` is the one left by the last event stamped before `t`. -/
theorem cacheBefore_of_split {schedule : Schedule Page} {t : Time}
    {A : List (FetchEvent Page)} {e : FetchEvent Page} {B : List (FetchEvent Page)}
    (hsplit : schedule.events = A ++ e :: B) (he : e.time < t)
    (hB : ∀ x ∈ B, t ≤ x.time) : schedule.cacheBefore t = e.cacheAfter := by
  unfold Schedule.cacheBefore
  rw [hsplit, show A ++ e :: B = (A ++ [e]) ++ B by simp, List.foldl_append,
    List.foldl_append, List.foldl_cons, List.foldl_nil, if_pos he]
  exact foldl_noop t B _ fun x hx => not_lt.mpr (hB x hx)

/-- **The comparator's cache is `heldCache (swapBC r 2)` throughout phase `r`.** -/
theorem comparator_cacheBefore {k : ℕ} (pages : Fin (k + 2) ↪ Page)
    {runs r : ℕ} (hr : r ≤ runs) {t : Time} (hlt : phaseTime k r < t)
    (hge : ∀ r', r < r' → r' ≤ runs → t ≤ phaseTime k r')
    (hfin : t ≤ finalTime k runs) :
    (comparator k runs pages).cacheBefore t = heldCache k pages (swapBC r 2) := by
  have hsplit : (comparator k runs pages).events =
      (List.range' 0 r).map (phaseEvent k pages) ++
        phaseEvent k pages r ::
          ((List.range' (r + 1) (runs - r)).map (phaseEvent k pages) ++
            [finalEvent k runs pages]) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hr
    simp [comparator, compEvents, show r + n + 1 = r + (n + 1) by omega, ← List.range'_append_1,
      List.range'_succ]
  refine cacheBefore_of_split hsplit hlt fun x hx => ?_
  simp only [List.mem_append, List.mem_map, List.mem_range'_1, List.mem_singleton] at hx
  rcases hx with ⟨r', _, rfl⟩ | rfl
  exacts [hge r' (by omega) (by omega), hfin]

end
end PagingWithDelay.LowerBound
