import Proofs.LowerBound.Codes
import Proofs.Competitive.AlgorithmCost

/-!
# Replaying the FIFO event loop on the adversarial instance

Bookkeeping for the step-by-step replay of `FIFO.run` on `input δ k runs pages hk`:
the queue after `i` fetches, the occurrences still unseen after `i` arrivals,
and the arithmetic of the run structure.
-/

namespace PagingWithDelay.LowerBound

open PagingWithDelay.FIFO

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-! ## Run arithmetic -/

theorem mod_run (k r q : ℕ) (h : q < runLength k) :
    (runLength k * r + q) % runLength k = q := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h]

theorem div_run (k r q : ℕ) (h : q < runLength k) :
    (runLength k * r + q) / runLength k = r := by
  rw [Nat.mul_add_div (runLength_pos k), Nat.div_eq_of_lt h, Nat.add_zero]

theorem run_index_lt {k r q runs : ℕ} (hr : r < runs) (hq : q < runLength k) :
    runLength k * r + q < runLength k * runs := by
  have h : runLength k * (r + 1) ≤ runLength k * runs := Nat.mul_le_mul_left _ hr
  have e : runLength k * (r + 1) = runLength k * r + runLength k := by ring
  omega

/-! ## The page codes along the criticality order -/

theorem pageCode_run (k r q : ℕ) (h : q < runLength k) :
    pageCode k (runLength k * r + q) = swapBC r (codeAt k (critPos k q)) := by
  unfold pageCode
  rw [mod_run k r q h, div_run k r q h]

/-- Away from the transposed pair, the request that arrives `q`-th in a run is
also the one fetched `q+1`-st. -/
theorem pageCode_generic (k r q : ℕ) (h : q < runLength k)
    (h1 : q ≠ k + 1) (h2 : q ≠ k + 2) :
    pageCode k (runLength k * r + q) = fetchedCode k (runLength k * r + q + 1) := by
  have hL : runLength k = 2 * k + 2 := rfl
  rw [pageCode_run k r q h, show critPos k q = q + 1 by unfold critPos; rw [if_neg h1, if_neg h2],
    show runLength k * r + q + 1 = runLength k * r + (q + 1) by ring,
    fetchedCode_eq k r (q + 1) (by omega) (by omega)]

/-- The early repeat request is the one fetched two positions later. -/
theorem pageCode_early (k r : ℕ) (hk : 0 < k) :
    pageCode k (runLength k * r + (k + 1)) = fetchedCode k (runLength k * r + (k + 3)) := by
  have hL : runLength k = 2 * k + 2 := rfl
  rw [pageCode_run k r (k + 1) (by omega), fetchedCode_eq k r (k + 3) (by omega) (by omega)]
  simp [critPos]

/-- The overtaken request keeps its own fetch position. -/
theorem pageCode_late (k r : ℕ) (hk : 0 < k) :
    pageCode k (runLength k * r + (k + 2)) = fetchedCode k (runLength k * r + (k + 2)) := by
  have hL : runLength k = 2 * k + 2 := rfl
  rw [pageCode_run k r (k + 2) (by omega), fetchedCode_eq k r (k + 2) (by omega) (by omega)]
  simp [critPos]

theorem pageCode_lt (k m : ℕ) (hk : 0 < k) : pageCode k m < k + 2 := by
  have hmod : m % runLength k < 2 * k + 2 := Nat.mod_lt m (runLength_pos k)
  exact swapBC_lt k _ _ (codeAt_lt k _ hk (by unfold critPos; split_ifs <;> omega)
    (by unfold critPos; split_ifs <;> omega)) hk

/-- The `b` and `c` of one run are different pages. -/
theorem pageCode_early_ne_late (k r : ℕ) (hk : 0 < k) :
    pageCode k (runLength k * r + (k + 1)) ≠ pageCode k (runLength k * r + (k + 2)) := by
  rw [pageCode_early k r hk, pageCode_late k r hk]
  exact (fetchedCode_ne hk (by omega) (by omega) (by omega)).symm

/-! ## The queue -/

/-- The page carried by the `i`-th fetch. -/
def fetchedPage (k : ℕ) (pages : Fin (k + 2) ↪ Page) (i : ℕ) : Page :=
  page k pages (fetchedCode k i)

/-- The page at position `n` of the eviction order. -/
def entryPage (k : ℕ) (pages : Fin (k + 2) ↪ Page) (n : ℕ) : Page :=
  page k pages (entryCode k n)

/-- FIFO's queue once `i` payments have been made: the `k` entries
`i, …, i + k - 1` of the eviction order, oldest first. -/
def queueAt (k : ℕ) (pages : Fin (k + 2) ↪ Page) (i : ℕ) : List Page :=
  (List.range' i k).map (entryPage k pages)

omit [DecidableEq Page] in
theorem queueAt_zero (k : ℕ) (pages : Fin (k + 2) ↪ Page) :
    queueAt k pages 0 = initialCache k pages := by
  unfold queueAt initialCache
  rw [List.range_eq_range']
  apply List.map_congr_left
  intro n hn
  rw [List.mem_range'_1] at hn
  simp [entryPage, entryCode_of_lt (show n < k by omega)]

omit [DecidableEq Page] in
theorem queueAt_length (k : ℕ) (pages : Fin (k + 2) ↪ Page) (i : ℕ) :
    (queueAt k pages i).length = k := by
  simp [queueAt]

omit [DecidableEq Page] in
theorem mem_queueAt {k : ℕ} {pages : Fin (k + 2) ↪ Page} {i : ℕ} {p : Page}
    (h : p ∈ queueAt k pages i) :
    ∃ n, i ≤ n ∧ n < i + k ∧ p = entryPage k pages n := by
  simp only [queueAt, List.mem_map, List.mem_range'_1] at h
  obtain ⟨n, ⟨hlo, hhi⟩, hn⟩ := h
  exact ⟨n, hlo, hhi, hn.symm⟩

omit [DecidableEq Page] in
theorem entryPage_of_ge {k : ℕ} (pages : Fin (k + 2) ↪ Page) {n : ℕ} (hn : k ≤ n) :
    entryPage k pages n = fetchedPage k pages (n - k + 1) := by
  simp [entryPage, fetchedPage, entryCode_of_ge hn]

omit [DecidableEq Page] in
/-- One fetch advances the queue. -/
theorem queueAt_succ (k : ℕ) (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) (i : ℕ) :
    insertPage k (queueAt k pages i) (fetchedPage k pages (i + 1)) = queueAt k pages (i + 1) := by
  have hlen : (queueAt k pages i).length = k := queueAt_length k pages i
  rw [insertPage, if_neg (by rw [hlen]; omega)]
  unfold queueAt
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [List.range'_succ, List.map_cons, List.tail_cons, List.range'_concat, List.map_append,
    List.map_singleton, entryPage_of_ge pages (by omega),
    show i + 1 + 1 * k' - (k' + 1) + 1 = i + 1 by omega]

omit [DecidableEq Page] in
/-- A page that no entry of the window carries is absent from the queue. -/
theorem notMem_queueAt {k : ℕ} (hk : 0 < k) {pages : Fin (k + 2) ↪ Page} {i c : ℕ}
    (hc : c < k + 2)
    (hne : ∀ n, i ≤ n → n < i + k → entryCode k n ≠ c) :
    page k pages c ∉ queueAt k pages i := by
  intro hmem
  obtain ⟨n, hlo, hhi, hn⟩ := mem_queueAt hmem
  exact hne n hlo hhi (page_injOn pages (entryCode_lt k n hk) hc hn.symm)

/-! ## The unseen occurrences -/

/-- The occurrence of the request with global arrival rank `m`. -/
def occAt (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) (m : ℕ) : Occurrence Page :=
  { id := m, request := requestAt δ k runs pages m }

/-- The occurrences that have not arrived yet once the first `j` have. -/
def unseenFrom (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) (j : ℕ) :
    List (Occurrence Page) :=
  (List.range' j (runLength k * runs - j)).map (occAt δ k runs pages)

omit [DecidableEq Page] in
theorem unseenFrom_cons (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) {j : ℕ}
    (h : j < runLength k * runs) :
    unseenFrom δ k runs pages j =
      occAt δ k runs pages j :: unseenFrom δ k runs pages (j + 1) := by
  unfold unseenFrom
  rw [show runLength k * runs - j = (runLength k * runs - (j + 1)) + 1 by omega]
  rfl

omit [DecidableEq Page] in
theorem unseenFrom_nil (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) {j : ℕ}
    (h : runLength k * runs ≤ j) : unseenFrom δ k runs pages j = [] := by
  unfold unseenFrom
  rw [show runLength k * runs - j = 0 by omega]
  rfl

omit [DecidableEq Page] in
theorem unseenFrom_tail (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) (j : ℕ) :
    (unseenFrom δ k runs pages j).tail = unseenFrom δ k runs pages (j + 1) := by
  rcases Nat.lt_or_ge j (runLength k * runs) with h | h
  · rw [unseenFrom_cons δ k runs pages h]; rfl
  · rw [unseenFrom_nil δ k runs pages h, unseenFrom_nil δ k runs pages (by omega)]; rfl

omit [DecidableEq Page] in
theorem enumerateFrom_range' (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) :
    ∀ (len j : ℕ), enumerateFrom j ((List.range' j len).map (requestAt δ k runs pages)) =
      (List.range' j len).map (occAt δ k runs pages)
  | 0, _ => rfl
  | len + 1, j => congrArg (occAt δ k runs pages j :: ·) (enumerateFrom_range' δ k runs pages len (j + 1))

omit [DecidableEq Page] in
theorem unseenFrom_zero (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) (hk : 0 < k) :
    enumerate (input δ k runs pages hk).requests = unseenFrom δ k runs pages 0 := by
  simpa [unseenFrom, List.range_eq_range'] using enumerateFrom_range' δ k runs pages _ 0

end
end PagingWithDelay.LowerBound
