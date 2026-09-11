import PagingWithDelay.Model

/-!
# Offline schedules for the deadline certificate

The certificate of `nonlazy-lower-bound.tex` asserts the existence of offline
schedules reaching prescribed configurations at prescribed cost, having served
prescribed requests inside their windows.  This file is the vocabulary those
assertions need, in the form the drafts use it — servers on a uniform metric,
i.e. a cache of a fixed size — and with the *service semantics of
`Model.lean`*: a request is served when its page is in the cache at the moment
the request arrives, or when it is fetched at or after that moment.

A schedule here is a start configuration plus a list of timed moves, each
fetching one page and evicting one.  `Reaches start served now cost cfg` is the
one predicate the certificate uses: *some* such schedule has at most `cost`
moves, all stamped no later than `now`, ends in configuration `cfg`, and has
served every request in `served` within its window.

Nothing in this file is specific to the adversary; `Certificate.lean` is where
the drafts' invariant and its two operations live.
-/

namespace PagingWithDelay.DeadlineLowerBound

open Finset

noncomputable section

variable {Page : Type*} [DecidableEq Page]

/-- A request reduced to what the offline certificate reads: a page and a
closed window.  `Charging.lean` relates this to a `Request` of `Model.lean`
carrying a deadline-shaped delay curve. -/
structure Window (Page : Type*) where
  page : Page
  arrival : Time
  deadline : Time

/-- One offline move: at `time`, fetch `fetched` and evict `evicted`. -/
structure Move (Page : Type*) where
  time : Time
  fetched : Page
  evicted : Page

/-- The cache after one move. -/
def applyMove (cache : Finset Page) (mv : Move Page) : Finset Page :=
  insert mv.fetched (cache.erase mv.evicted)

/-- The cache after a list of moves. -/
def cacheAfter (start : Finset Page) (moves : List (Move Page)) : Finset Page :=
  moves.foldl applyMove start

@[simp] theorem cacheAfter_nil (start : Finset Page) : cacheAfter start [] = start := rfl

theorem cacheAfter_append (start : Finset Page) (first second : List (Move Page)) :
    cacheAfter start (first ++ second) = cacheAfter (cacheAfter start first) second := by
  simp [cacheAfter, List.foldl_append]

/-- Each move evicts a page it holds and fetches one it does not, so the cache
size never changes. -/
def ValidMoves (start : Finset Page) : List (Move Page) → Prop
  | [] => True
  | mv :: rest => mv.evicted ∈ start ∧ mv.fetched ∉ start ∧ ValidMoves (applyMove start mv) rest

theorem validMoves_append {start : Finset Page} {first second : List (Move Page)}
    (hfirst : ValidMoves start first) (hsecond : ValidMoves (cacheAfter start first) second) :
    ValidMoves start (first ++ second) := by
  induction first generalizing start with
  | nil => simpa [cacheAfter] using hsecond
  | cons mv rest ih =>
      obtain ⟨hevict, hfetch, hrest⟩ := hfirst
      exact ⟨hevict, hfetch, ih hrest (by simpa [cacheAfter] using hsecond)⟩

theorem card_applyMove {cache : Finset Page} {mv : Move Page} (hevict : mv.evicted ∈ cache)
    (hfetch : mv.fetched ∉ cache) : (applyMove cache mv).card = cache.card := by
  have hnot : mv.fetched ∉ cache.erase mv.evicted := fun h => hfetch (Finset.mem_of_mem_erase h)
  rw [applyMove, Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem hevict]
  have : 1 ≤ cache.card := Finset.card_pos.mpr ⟨mv.evicted, hevict⟩
  omega

theorem card_cacheAfter {start : Finset Page} :
    ∀ {moves : List (Move Page)}, ValidMoves start moves →
      (cacheAfter start moves).card = start.card := by
  intro moves
  induction moves generalizing start with
  | nil => intro _; rfl
  | cons mv rest ih =>
      rintro ⟨hevict, hfetch, hrest⟩
      have := ih hrest
      simp only [cacheAfter, List.foldl_cons] at this ⊢
      rw [this, card_applyMove hevict hfetch]

/-- The cache immediately before time `t`: the moves stamped strictly earlier. -/
def cacheBefore (start : Finset Page) (moves : List (Move Page)) (t : Time) : Finset Page :=
  cacheAfter start (moves.filter fun mv => decide (mv.time < t))

/-- A request is served when its page is in the cache as it arrives, or is
fetched inside its window.  This is `Model.lean`'s `serviceCandidates`, read
off a move list. -/
def Serves (start : Finset Page) (moves : List (Move Page)) (w : Window Page) : Prop :=
  w.page ∈ cacheBefore start moves w.arrival ∨
    ∃ mv ∈ moves, mv.fetched = w.page ∧ w.arrival ≤ mv.time ∧ mv.time ≤ w.deadline

/-- **The certificate's assertion.**  Some schedule from `start` with at most
`cost` moves, none of them later than `now`, ends at `cfg` and has served every
request of `served` inside its window. -/
def Reaches (start : Finset Page) (served : List (Window Page)) (now : Time) (cost : ℕ)
    (cfg : Finset Page) : Prop :=
  ∃ moves : List (Move Page),
    ValidMoves start moves ∧
    moves.Pairwise (fun earlier later => earlier.time < later.time) ∧
    (∀ mv ∈ moves, mv.time ≤ now) ∧
    moves.length ≤ cost ∧
    (∀ w ∈ served, Serves start moves w) ∧
    cacheAfter start moves = cfg

theorem Reaches.mono_cost {start : Finset Page} {served now cfg} {cost cost' : ℕ}
    (h : Reaches start served now cost cfg) (hle : cost ≤ cost') :
    Reaches start served now cost' cfg := by
  obtain ⟨moves, hvalid, hchrono, htimes, hlen, hserves, hcfg⟩ := h
  exact ⟨moves, hvalid, hchrono, htimes, hlen.trans hle, hserves, hcfg⟩

theorem Reaches.mono_now {start : Finset Page} {served cost cfg} {now now' : Time}
    (h : Reaches start served now cost cfg) (hle : now ≤ now') :
    Reaches start served now' cost cfg := by
  obtain ⟨moves, hvalid, hchrono, htimes, hlen, hserves, hcfg⟩ := h
  exact ⟨moves, hvalid, hchrono, fun mv hmv => (htimes mv hmv).trans hle, hlen, hserves, hcfg⟩

theorem Reaches.subset {start : Finset Page} {served served' : List (Window Page)} {now cost cfg}
    (h : Reaches start served now cost cfg) (hsub : ∀ w ∈ served', w ∈ served) :
    Reaches start served' now cost cfg := by
  obtain ⟨moves, hvalid, hchrono, htimes, hlen, hserves, hcfg⟩ := h
  exact ⟨moves, hvalid, hchrono, htimes, hlen, fun w hw => hserves w (hsub w hw), hcfg⟩

/-! ## Two ways to serve one more request -/

/-- A schedule that is sitting on the page when the request arrives serves it
for free.  This is the drafts' "the cheap candidate covers `x`, so it serves the
expiring request without moving". -/
theorem Reaches.serves_of_mem {start : Finset Page} {served now cost cfg}
    (h : Reaches start served now cost cfg) (w : Window Page) (hmem : w.page ∈ cfg)
    (harrival : now < w.arrival) : Reaches start (w :: served) now cost cfg := by
  obtain ⟨moves, hvalid, hchrono, htimes, hlen, hserves, hcfg⟩ := h
  refine ⟨moves, hvalid, hchrono, htimes, hlen, ?_, hcfg⟩
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · left
    have hfilter : moves.filter (fun mv => decide (mv.time < v.arrival)) = moves := by
      apply List.filter_eq_self.mpr
      intro mv hmv
      exact decide_eq_true (lt_of_le_of_lt (htimes mv hmv) harrival)
    rw [cacheBefore, hfilter, hcfg]
    exact hmem
  · exact hserves v hv

/-! ## Extending a schedule by one move -/

/-- Appending a move stamped no earlier than a request's arrival cannot unserve
it. -/
theorem serves_append {start : Finset Page} {moves extra : List (Move Page)} {w : Window Page}
    (hserves : Serves start moves w) (hlate : ∀ mv ∈ extra, w.arrival ≤ mv.time) :
    Serves start (moves ++ extra) w := by
  rcases hserves with hmem | ⟨mv, hmv, hpage, hafter, hbefore⟩
  · left
    have hfilter : extra.filter (fun mv => decide (mv.time < w.arrival)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro mv hmv
      simpa using not_lt_of_ge (hlate mv hmv)
    rwa [cacheBefore, List.filter_append, hfilter, List.append_nil]
  · exact Or.inr ⟨mv, List.mem_append_left _ hmv, hpage, hafter, hbefore⟩

/-- One more move, at a time after everything so far.  The requests in `extra`
are the ones this move itself serves: it fetches their page inside their
window. -/
theorem Reaches.append_move {start : Finset Page} {served : List (Window Page)} {now cost cfg}
    (h : Reaches start served now cost cfg) (mv : Move Page) (htime : now < mv.time)
    (hevict : mv.evicted ∈ cfg) (hfetch : mv.fetched ∉ cfg)
    (harrivals : ∀ w ∈ served, w.arrival ≤ mv.time) (extra : List (Window Page))
    (hextra : ∀ w ∈ extra, mv.fetched = w.page ∧ w.arrival ≤ mv.time ∧ mv.time ≤ w.deadline) :
    Reaches start (extra ++ served) mv.time (cost + 1) (applyMove cfg mv) := by
  obtain ⟨moves, hvalid, hchrono, htimes, hlen, hserves, hcfg⟩ := h
  refine ⟨moves ++ [mv], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact validMoves_append hvalid (by rw [hcfg]; exact ⟨hevict, hfetch, trivial⟩)
  · rw [List.pairwise_append]
    refine ⟨hchrono, List.pairwise_singleton _ _, ?_⟩
    intro earlier hearlier later hlater
    rw [List.mem_singleton] at hlater
    exact hlater ▸ lt_of_le_of_lt (htimes earlier hearlier) htime
  · intro candidate hcandidate
    rcases List.mem_append.mp hcandidate with hmem | hmem
    · exact (htimes candidate hmem).trans htime.le
    · rw [List.mem_singleton] at hmem
      exact hmem ▸ le_rfl
  · simpa using Nat.succ_le_succ hlen
  · intro w hw
    rcases List.mem_append.mp hw with hnew | hold
    · obtain ⟨hpage, hafter, hbefore⟩ := hextra w hnew
      exact Or.inr ⟨mv, List.mem_append_right _ (by simp), hpage, hafter, hbefore⟩
    · exact serves_append (hserves w hold) (by
        intro candidate hcandidate
        rw [List.mem_singleton] at hcandidate
        exact hcandidate ▸ harrivals w hold)
  · rw [cacheAfter_append, hcfg]
    rfl

/-- One more move that serves nothing new. -/
theorem Reaches.step {start : Finset Page} {served : List (Window Page)} {now cost cfg}
    (h : Reaches start served now cost cfg) (mv : Move Page) (htime : now < mv.time)
    (hevict : mv.evicted ∈ cfg) (hfetch : mv.fetched ∉ cfg)
    (harrivals : ∀ w ∈ served, w.arrival ≤ mv.time) :
    Reaches start served mv.time (cost + 1) (applyMove cfg mv) := by
  simpa using h.append_move mv htime hevict hfetch harrivals [] (by simp)

/-- One more move, serving a request whose page it fetches inside the window. -/
theorem Reaches.step_serving {start : Finset Page} {served : List (Window Page)} {now cost cfg}
    (h : Reaches start served now cost cfg) (mv : Move Page) (w : Window Page)
    (htime : now < mv.time) (hevict : mv.evicted ∈ cfg) (hfetch : mv.fetched ∉ cfg)
    (harrivals : ∀ v ∈ served, v.arrival ≤ mv.time)
    (hpage : mv.fetched = w.page) (hafter : w.arrival ≤ mv.time) (hbefore : mv.time ≤ w.deadline) :
    Reaches start (w :: served) mv.time (cost + 1) (applyMove cfg mv) := by
  simpa using h.append_move mv htime hevict hfetch harrivals [w]
    (by intro v hv; rw [List.mem_singleton] at hv; exact hv ▸ ⟨hpage, hafter, hbefore⟩)

end
end PagingWithDelay.DeadlineLowerBound
