import PagingWithDelay.LowerBound.Codes
import PagingWithDelay.Competitive.AlgorithmCost

/-!
# Replaying the FIFO event loop on the adversarial instance

Bookkeeping for the step-by-step replay of `FIFO.run` on `input δ k runs pages`:
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
  rw [pageCode_run k r (k + 1) (by omega),
    show critPos k (k + 1) = k + 3 by unfold critPos; rw [if_pos rfl],
    fetchedCode_eq k r (k + 3) (by omega) (by omega)]

/-- The overtaken request keeps its own fetch position. -/
theorem pageCode_late (k r : ℕ) (hk : 0 < k) :
    pageCode k (runLength k * r + (k + 2)) = fetchedCode k (runLength k * r + (k + 2)) := by
  have hL : runLength k = 2 * k + 2 := rfl
  rw [pageCode_run k r (k + 2) (by omega),
    show critPos k (k + 2) = k + 2 by
      unfold critPos; rw [if_neg (by omega), if_pos rfl],
    fetchedCode_eq k r (k + 2) (by omega) (by omega)]

theorem critPos_bounds (k q : ℕ) (hk : 0 < k) (h : q < runLength k) :
    1 ≤ critPos k q ∧ critPos k q ≤ 2 * k + 2 := by
  have hL : runLength k = 2 * k + 2 := rfl
  unfold critPos
  split_ifs <;> omega

theorem pageCode_lt (k m : ℕ) (hk : 0 < k) : pageCode k m < k + 2 := by
  have hmod : m % runLength k < runLength k := Nat.mod_lt m (runLength_pos k)
  obtain ⟨h1, h2⟩ := critPos_bounds k (m % runLength k) hk hmod
  exact swapBC_lt k _ _ (codeAt_lt k _ hk h1 h2) hk

/-- The `b` and `c` of one run are different pages. -/
theorem pageCode_early_ne_late (k r : ℕ) (hk : 0 < k) :
    pageCode k (runLength k * r + (k + 1)) ≠ pageCode k (runLength k * r + (k + 2)) := by
  have hL : runLength k = 2 * k + 2 := rfl
  rw [pageCode_run k r (k + 1) (by omega), pageCode_run k r (k + 2) (by omega),
    show critPos k (k + 1) = k + 3 by unfold critPos; rw [if_pos rfl],
    show critPos k (k + 2) = k + 2 by unfold critPos; rw [if_neg (by omega), if_pos rfl],
    show codeAt k (k + 3) = 2 by unfold codeAt; split_ifs <;> omega,
    show codeAt k (k + 2) = 1 by unfold codeAt; split_ifs <;> omega]
  intro h
  exact absurd (swapBC_injective r h) (by omega)

/-- The extra separation needed by the transposed pair: `a` is fetched `k+1`
positions before the repeat request on `c`, and they are different pages. -/
theorem fetchedCode_a_ne (k r : ℕ) (hk : 0 < k) :
    fetchedCode k (runLength k * r + 2) ≠ fetchedCode k (runLength k * r + (k + 3)) := by
  have hL : runLength k = 2 * k + 2 := rfl
  rw [fetchedCode_eq k r 2 (by omega) (by omega),
    fetchedCode_eq k r (k + 3) (by omega) (by omega),
    show codeAt k 2 = 0 by unfold codeAt; split_ifs <;> omega,
    show codeAt k (k + 3) = 2 by unfold codeAt; split_ifs <;> omega]
  unfold swapBC
  split_ifs <;> omega

/-! ## The queue -/

/-- The page carried by the `i`-th fetch. -/
def fetchedPage (k : ℕ) (pages : Fin (k + 2) ↪ Page) (i : ℕ) : Page :=
  page k pages (fetchedCode k i)

/-- FIFO's queue once `i` payments have been made: the last `min i k` fetched
pages, oldest first. -/
def queueAt (k : ℕ) (pages : Fin (k + 2) ↪ Page) (i : ℕ) : List Page :=
  (List.range' (i + 1 - min i k) (min i k)).map (fetchedPage k pages)

omit [DecidableEq Page] in
theorem queueAt_length (k : ℕ) (pages : Fin (k + 2) ↪ Page) (i : ℕ) :
    (queueAt k pages i).length = min i k := by
  simp [queueAt]

omit [DecidableEq Page] in
theorem mem_queueAt {k : ℕ} {pages : Fin (k + 2) ↪ Page} {i : ℕ} {p : Page}
    (h : p ∈ queueAt k pages i) :
    ∃ j, i + 1 - min i k ≤ j ∧ j ≤ i ∧ p = fetchedPage k pages j := by
  simp only [queueAt, List.mem_map, List.mem_range'_1] at h
  obtain ⟨j, ⟨hlo, hhi⟩, hj⟩ := h
  exact ⟨j, hlo, by omega, hj.symm⟩

omit [DecidableEq Page] in
/-- One fetch advances the queue. -/
theorem queueAt_succ (k : ℕ) (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) (i : ℕ) :
    insertPage k (queueAt k pages i) (fetchedPage k pages (i + 1)) = queueAt k pages (i + 1) := by
  have hlen : (queueAt k pages i).length = min i k := queueAt_length k pages i
  rcases Nat.lt_or_ge i k with hlt | hge
  · have hmin : min i k = i := by omega
    have hmin' : min (i + 1) k = i + 1 := by omega
    rw [insertPage, if_pos (by rw [hlen, hmin]; omega)]
    unfold queueAt
    rw [hmin, hmin', show i + 1 - i = 1 by omega, show i + 1 + 1 - (i + 1) = 1 by omega,
      List.range'_concat, List.map_append]
    norm_num
    congr 1
    omega
  · have hmin : min i k = k := by omega
    have hmin' : min (i + 1) k = k := by omega
    rw [insertPage, if_neg (by rw [hlen, hmin]; omega)]
    unfold queueAt
    rw [hmin, hmin']
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [List.range'_succ, List.map_cons, List.tail_cons,
      show i + 1 + 1 - (k' + 1) = i + 1 - (k' + 1) + 1 by omega,
      List.range'_concat,
      show i + 1 - (k' + 1) + 1 + 1 * k' = i + 1 by omega,
      List.map_append]
    rfl

omit [DecidableEq Page] in
/-- A page that no fetch in the window carries is absent from the queue. -/
theorem notMem_queueAt {k : ℕ} (hk : 0 < k) {pages : Fin (k + 2) ↪ Page} {i c : ℕ}
    (hc : c < k + 2)
    (hne : ∀ j, i + 1 - min i k ≤ j → j ≤ i → fetchedCode k j ≠ c) :
    page k pages c ∉ queueAt k pages i := by
  intro hmem
  obtain ⟨j, hlo, hhi, hj⟩ := mem_queueAt hmem
  exact hne j hlo hhi (page_injOn pages (fetchedCode_lt k j hk) hc hj.symm)

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
      (List.range' j len).map (occAt δ k runs pages) := by
  intro len
  induction len with
  | zero => intro j; rfl
  | succ len ih =>
      intro j
      rw [show List.range' j (len + 1) = j :: List.range' (j + 1) len from rfl]
      simp only [List.map_cons, enumerateFrom]
      rw [ih (j + 1)]
      rfl

omit [DecidableEq Page] in
theorem unseenFrom_zero (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) :
    enumerate (input δ k runs pages).requests = unseenFrom δ k runs pages 0 := by
  show enumerateFrom 0 ((List.range (runLength k * runs)).map (requestAt δ k runs pages)) = _
  rw [List.range_eq_range']
  rw [enumerateFrom_range' δ k runs pages (runLength k * runs) 0]
  unfold unseenFrom
  rw [Nat.sub_zero]

end
end PagingWithDelay.LowerBound
