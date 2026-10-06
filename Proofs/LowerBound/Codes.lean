import Proofs.LowerBound.Construction

/-!
# Which page the `i`-th fetch of the adversarial instance carries

FIFO pays for the pending requests in criticality order, so its `i`-th fetch
carries the page whose criticality position is `i`.  This file gives that page
code a name, `fetchedCode`, and proves the combinatorial heart of the lower
bound: **any `k + 1` consecutive fetches are on distinct pages**
(`fetchedCode_ne`), together with the one extra separation the transposed pair
of a run needs (`fetchedCode_a_ne`).

Both are statements about `codeAt` and `swapBC` alone; the timing of the
instance plays no part in them.
-/

namespace PagingWithDelay.LowerBound

theorem runLength_pos (k : ℕ) : 0 < runLength k := by unfold runLength; omega

/-- Page code fetched by the `i`-th threshold payment, counted from `1`. -/
def fetchedCode (k i : ℕ) : ℕ :=
  swapBC ((i - 1) / runLength k) (codeAt k ((i - 1) % runLength k + 1))

theorem fetchedCode_lt (k i : ℕ) (hk : 0 < k) : fetchedCode k i < k + 2 := by
  have hmod : (i - 1) % runLength k < 2 * k + 2 := Nat.mod_lt (i - 1) (runLength_pos k)
  exact swapBC_lt k _ _ (codeAt_lt k _ hk (by omega) (by omega)) hk

/-- Splitting the fetch index into run and criticality position. -/
theorem fetchedCode_eq (k r j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ runLength k) :
    fetchedCode k (runLength k * r + j) = swapBC r (codeAt k j) := by
  have hL := runLength_pos k
  have hsub : runLength k * r + j - 1 = runLength k * r + (j - 1) := by omega
  have hlt : j - 1 < runLength k := by omega
  unfold fetchedCode
  rw [hsub, Nat.mul_add_div hL, Nat.mul_add_mod, Nat.div_eq_of_lt hlt,
    Nat.mod_eq_of_lt hlt]
  simp only [Nat.add_zero]
  congr 2
  omega

/-! ## Distinctness -/

/-- Inside one run, two criticality positions at distance at most `k` carry
different pages. -/
theorem codeAt_ne_of_close {k j j' : ℕ} (hk : 0 < k) (h1 : 1 ≤ j) (hlt : j < j')
    (hle : j' ≤ j + k) (hj' : j' ≤ 2 * k + 2) : codeAt k j ≠ codeAt k j' := by
  unfold codeAt
  split_ifs <;> omega

/-- The relabelling of one run, as a function of page codes. -/
def swap12 (code : ℕ) : ℕ := if code = 1 then 2 else if code = 2 then 1 else code

theorem swapBC_injective (r : ℕ) : Function.Injective (swapBC r) := by
  intro x y h
  unfold swapBC at h
  split_ifs at h <;> omega

theorem swapBC_succ (r code : ℕ) : swapBC (r + 1) code = swapBC r (swap12 code) := by
  unfold swapBC swap12
  split_ifs <;> omega

/-- Across a run boundary the roles of `b` and `c` are exchanged, and the
positions are at distance at least `k + 2` inside their runs. -/
theorem codeAt_swap_ne {k r j j' : ℕ} (hk : 0 < k) (h1 : 1 ≤ j')
    (hj : j ≤ 2 * k + 2) (hgap : j' + k + 2 ≤ j) :
    swapBC r (codeAt k j) ≠ swapBC (r + 1) (codeAt k j') := by
  have hjk : j' ≤ k := by omega
  rw [swapBC_succ]
  intro hcontra
  have h := swapBC_injective r hcontra
  have hjval : codeAt k j = 2 ∨ (k + 4 ≤ j ∧ codeAt k j = 2 * k + 5 - j) := by
    unfold codeAt; split_ifs <;> omega
  have hj'val : codeAt k j' = 2 ∨ codeAt k j' = 0 ∨ (3 ≤ j' ∧ codeAt k j' = k + 4 - j') := by
    unfold codeAt; split_ifs <;> omega
  rcases hjval with hv | ⟨hb, hv⟩ <;> rcases hj'val with hw | hw | ⟨hb', hw⟩ <;>
    rw [hv, hw] at h <;> simp only [swap12] at h <;> split_ifs at h <;> omega

/-- Every fetch index has a run and a criticality position inside it. -/
theorem exists_run_pos (k i : ℕ) (hi : 1 ≤ i) :
    ∃ r j, i = runLength k * r + j ∧ 1 ≤ j ∧ j ≤ runLength k := by
  refine ⟨(i - 1) / runLength k, (i - 1) % runLength k + 1, ?_, by omega, ?_⟩
  · have := Nat.div_add_mod (i - 1) (runLength k)
    omega
  · have := Nat.mod_lt (i - 1) (runLength_pos k)
    omega

/-- **Any `k + 1` consecutive fetches are on distinct pages.** -/
theorem fetchedCode_ne {k : ℕ} (hk : 0 < k) {i i' : ℕ} (hi : 1 ≤ i) (hlt : i < i')
    (hle : i' ≤ i + k) : fetchedCode k i ≠ fetchedCode k i' := by
  obtain ⟨r, j, rfl, hj1, hj2⟩ := exists_run_pos k i hi
  obtain ⟨r', j', rfl, hj1', hj2'⟩ := exists_run_pos k i' (by omega)
  have hLk : runLength k = 2 * k + 2 := rfl
  have h1 : r < r' + 1 := Nat.lt_of_mul_lt_mul_left (a := runLength k) (by rw [Nat.mul_succ]; omega)
  have h2 : r' < r + 2 := Nat.lt_of_mul_lt_mul_left (a := runLength k) (by
    rw [show runLength k * (r + 2) = runLength k * r + 2 * runLength k by ring]; omega)
  rw [fetchedCode_eq k r j hj1 hj2, fetchedCode_eq k r' j' hj1' hj2']
  obtain rfl | rfl : r' = r ∨ r' = r + 1 := by omega
  · exact fun h => codeAt_ne_of_close hk hj1 (by omega) (by omega) (by omega) (swapBC_injective r' h)
  · have : runLength k * (r + 1) = runLength k * r + runLength k := Nat.mul_succ _ _
    exact codeAt_swap_ne hk hj1' (by omega) (by omega)

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

/-! ## The eviction order -/

/-- The code at position `n` of the eviction order: the initial queue for
`n < k`, then the pages fetched by payments `1, 2, …`.  The entry at position
`n` is the page FIFO's `n`-th eviction removes, and the queue once `i`
payments have been made is the window of entries `i, …, i + k - 1`. -/
def entryCode (k n : ℕ) : ℕ :=
  if n < k then initialCode k n else fetchedCode k (n - k + 1)

theorem entryCode_of_lt {k n : ℕ} (hn : n < k) : entryCode k n = initialCode k n := by
  simp [entryCode, hn]

theorem entryCode_of_ge {k n : ℕ} (hn : k ≤ n) : entryCode k n = fetchedCode k (n - k + 1) := by
  simp [entryCode, not_lt.mpr hn]

theorem entryCode_lt (k n : ℕ) (hk : 0 < k) : entryCode k n < k + 2 := by
  unfold entryCode
  split_ifs with h
  · exact initialCode_lt k n hk h
  · exact fetchedCode_lt k _ hk

/-- A page of the initial queue differs from every page fetched while it is
still cached: the first run's fetches `c, a, v_{k-1}, …` reach `v_j` only
after `v_j` has been evicted. -/
theorem initialCode_ne_fetchedCode {k n j : ℕ} (hk : 0 < k) (hn : n < k) (hj1 : 1 ≤ j)
    (hj : j ≤ n + 1) : initialCode k n ≠ fetchedCode k j := by
  rw [show j = runLength k * 0 + j by simp, fetchedCode_eq k 0 j hj1 (by unfold runLength; omega)]
  unfold initialCode swapBC codeAt
  split_ifs <;> omega

/-- **Any `k + 1` consecutive entries of the eviction order are distinct.** -/
theorem entryCode_ne {k : ℕ} (hk : 0 < k) {n n' : ℕ} (hlt : n < n') (hle : n' ≤ n + k) :
    entryCode k n ≠ entryCode k n' := by
  by_cases hn' : n' < k
  · rw [entryCode_of_lt (hlt.trans hn'), entryCode_of_lt hn']
    intro h
    exact absurd (initialCode_injOn k (hlt.trans hn') hn' h) (by omega)
  · rw [entryCode_of_ge (not_lt.mp hn')]
    by_cases hn : n < k
    · rw [entryCode_of_lt hn]
      exact initialCode_ne_fetchedCode hk hn (by omega) (by omega)
    · rw [entryCode_of_ge (not_lt.mp hn)]
      exact fetchedCode_ne hk (by omega) (by omega) (by omega)

end PagingWithDelay.LowerBound
