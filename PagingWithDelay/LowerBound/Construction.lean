import PagingWithDelay.LowerBound.Curve

/-!
# The adversarial instance of "Tightness of the analysis"

The instance of the TeX proof, written out explicitly.  It uses `k + 2` pages,
named by codes

```text
0 = a,   1 = b,   2 = c,   3 … k+1 = v₁ … v_{k-1}
```

and consists of `runs` runs of `2k+2` requests each, starting from the initial
FIFO queue `b, v_{k-1}, …, v₁` (oldest first), which leaves `a` and `c`
absent.  In *criticality* order —
the order in which the pending requests reach the threshold `δ`, hence the
order in which FIFO fetches — a run is

```text
c, a, v_{k-1}, …, v₁, b, c, v_{k-1}, …, v₁
```

and consecutive runs exchange the roles of `b` and `c` (`swapBC`), so that the
next run again starts on the page FIFO evicted last.  Every `k+1` consecutive
requests are on distinct pages, which is what makes FIFO fault on all of them.

## Timing

Times are laid out in quarters.  The request whose criticality position in the
run is `j` reaches the threshold at `runLength * r + j` and arrives half a unit
earlier, so arrivals and payments strictly alternate and no request is issued
while FIFO still holds its page.

The one exception is the repeat request on `c` at position `k+3`: it is issued
*before* the request on `b` at position `k+2`, three quarters earlier than the
default, though it turns critical later.  This is the paper's "the request at
`c` that will turn critical after `b` turns critical is already issued", and it
is what lets the comparator serve both with a single fetch: it moves off `c`
only after that request has been issued and can be served from cache.

Arrival ranks therefore differ from criticality positions by the transposition
`critPos`.
-/

namespace PagingWithDelay.LowerBound

variable {Page : Type*}

noncomputable section

/-- Requests per run. -/
def runLength (k : ℕ) : ℕ := 2 * k + 2

/-- Criticality position (1-based, inside the run) of the request with arrival
rank `q` (0-based).  The identity `q ↦ q+1`, except that ranks `k+1` and `k+2`
carry the positions `k+3` and `k+2`. -/
def critPos (k q : ℕ) : ℕ :=
  if q = k + 1 then k + 3 else if q = k + 2 then k + 2 else q + 1

/-- The page code requested at criticality position `j` of a run. -/
def codeAt (k j : ℕ) : ℕ :=
  if j = 1 then 2                     -- c
  else if j = 2 then 0                -- a
  else if j ≤ k + 1 then k + 4 - j    -- v_{k-1} … v₁
  else if j = k + 2 then 1            -- b
  else if j = k + 3 then 2            -- c
  else 2 * k + 5 - j                  -- v_{k-1} … v₁

theorem codeAt_lt (k j : ℕ) (hk : 0 < k) (hj1 : 1 ≤ j) (hj : j ≤ 2 * k + 2) :
    codeAt k j < k + 2 := by
  unfold codeAt; split_ifs <;> omega

/-- Consecutive runs exchange `b` and `c`. -/
def swapBC (r code : ℕ) : ℕ :=
  if r % 2 = 0 then code else if code = 1 then 2 else if code = 2 then 1 else code

theorem swapBC_lt (k r code : ℕ) (h : code < k + 2) (hk : 0 < k) :
    swapBC r code < k + 2 := by
  unfold swapBC; split_ifs <;> omega

/-- Page code of the request with global arrival rank `m`. -/
def pageCode (k m : ℕ) : ℕ :=
  swapBC (m / runLength k) (codeAt k (critPos k (m % runLength k)))

/-- The `k+2` pages of the instance, drawn from the ambient page type. -/
def page (k : ℕ) (pages : Fin (k + 2) ↪ Page) (code : ℕ) : Page :=
  pages ⟨code % (k + 2), Nat.mod_lt _ (by omega)⟩

/-- Two codes below `k+2` name the same page only if they are equal. -/
theorem page_injOn {k : ℕ} (pages : Fin (k + 2) ↪ Page) {i j : ℕ}
    (hi : i < k + 2) (hj : j < k + 2) (h : page k pages i = page k pages j) : i = j := by
  have := pages.injective h
  simpa [Fin.ext_iff, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using this

/-- The code at position `n` of the initial FIFO queue `b, v_{k-1}, …, v₁`:
`b` at the front, then `v_{k-1}` down to `v₁`. -/
def initialCode (k n : ℕ) : ℕ := if n = 0 then 1 else k + 2 - n

theorem initialCode_lt (k n : ℕ) (hk : 0 < k) (hn : n < k) : initialCode k n < k + 2 := by
  unfold initialCode; split_ifs <;> omega

theorem initialCode_injOn (k : ℕ) {n n' : ℕ} (hn : n < k) (hn' : n' < k)
    (h : initialCode k n = initialCode k n') : n = n' := by
  unfold initialCode at h; split_ifs at h <;> omega

/-- The initial FIFO queue, oldest page first. -/
def initialCache (k : ℕ) (pages : Fin (k + 2) ↪ Page) : List Page :=
  (List.range k).map fun n => page k pages (initialCode k n)

@[simp] theorem initialCache_length (k : ℕ) (pages : Fin (k + 2) ↪ Page) :
    (initialCache k pages).length = k := by
  simp [initialCache]

theorem initialCache_nodup (k : ℕ) (hk : 0 < k) (pages : Fin (k + 2) ↪ Page) :
    (initialCache k pages).Nodup := by
  unfold initialCache
  refine List.nodup_range.map_on ?_
  intro n hn n' hn' h
  rw [List.mem_range] at hn hn'
  exact initialCode_injOn k hn hn'
    (page_injOn pages (initialCode_lt k n hk hn) (initialCode_lt k n' hk hn') h)


/-! ## Times, in quarters -/

/-- Arrival time of the request with global arrival rank `m`, in quarters.
The default is `4m+2`; the early repeat request on `c` (arrival rank `k+1`)
comes at `4m+1`, and the request on `b` it overtakes (rank `k+2`) at `4m-2`. -/
def arrivalQuarters (k m : ℕ) : ℕ :=
  if m % runLength k = k + 1 then 4 * m + 1
  else if m % runLength k = k + 2 then 4 * m - 2
  else 4 * m + 2

/-- Wait after which the request reaches the threshold, in quarters: half a
unit, except `7/4` for the early request. -/
def widthQuarters (k m : ℕ) : ℕ :=
  if m % runLength k = k + 1 then 7 else 2

theorem arrivalQuarters_le (k m : ℕ) : arrivalQuarters k m ≤ 4 * m + 2 := by
  unfold arrivalQuarters; split_ifs <;> omega

theorem le_arrivalQuarters_succ (k m : ℕ) : 4 * m + 2 ≤ arrivalQuarters k (m + 1) := by
  unfold arrivalQuarters; split_ifs <;> omega

theorem arrivalQuarters_mono (k : ℕ) : Monotone (arrivalQuarters k) :=
  monotone_nat_of_le_succ fun m =>
    (arrivalQuarters_le k m).trans (le_arrivalQuarters_succ k m)

def arrivalTime (k m : ℕ) : Time := (arrivalQuarters k m : Cost) / 4

def width (k m : ℕ) : Cost := (widthQuarters k m : Cost) / 4

theorem width_pos (k m : ℕ) : 0 < width k m := by
  unfold width widthQuarters
  split_ifs <;> norm_num

/-- The time at which this request reaches the threshold and FIFO fetches its
page. -/
def critTime (k m : ℕ) : Time := arrivalTime k m + width k m

theorem arrivalTime_mono (k : ℕ) : Monotone (arrivalTime k) := by
  intro m m' h
  unfold arrivalTime
  gcongr
  exact_mod_cast arrivalQuarters_mono k h

/-! ## The instance -/

/-- Where the delay tails start.  Every event of the instance — every arrival,
every threshold crossing, and the comparator's last fetch — happens before
this, so the curves are flat at `δ` throughout and neither algorithm ever pays
for a tail.  Its slope is therefore irrelevant, and taken to be `1`. -/
def horizon (k runs : ℕ) : Cost := ((runLength k * runs + 2 : ℕ) : Cost)

theorem two_le_horizon (k runs : ℕ) : (2 : Cost) ≤ horizon k runs := by
  unfold horizon
  exact_mod_cast Nat.le_add_left 2 _

theorem width_le (k m : ℕ) : width k m ≤ 7 / 4 := by
  unfold width widthQuarters
  split_ifs <;> · rw [← NNReal.coe_le_coe]; push_cast; norm_num

/-- A request reaches the threshold long before the tails start, so the
threshold is met exactly at `width` (`curve_at_width`). -/
theorem width_le_horizon (k runs m : ℕ) : width k m ≤ horizon k runs :=
  (width_le k m).trans
    (le_trans (by rw [← NNReal.coe_le_coe]; push_cast; norm_num) (two_le_horizon k runs))

/-- The request with global arrival rank `m`. -/
def requestAt (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) (m : ℕ) : Request Page :=
  LowerBound.request (page k pages (pageCode k m)) (arrivalTime k m) δ 1
    (width k m) (horizon k runs) one_pos

@[simp] theorem requestAt_arrival (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) (m : ℕ) :
    (requestAt δ k runs pages m).arrival = arrivalTime k m := rfl

@[simp] theorem requestAt_page (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) (m : ℕ) :
    (requestAt δ k runs pages m).page = page k pages (pageCode k m) := rfl

/-- The adversarial instance: `runs` runs of `2k+2` requests, cache size `k`,
starting from the initial queue `b, v_{k-1}, …, v₁`. -/
def input (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) : Instance Page where
  cacheSize := k
  initialCache := initialCache k pages
  requests := (List.range (runLength k * runs)).map (requestAt δ k runs pages)

@[simp] theorem input_initialCache (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) :
    (input δ k runs pages).initialCache = initialCache k pages := rfl

@[simp] theorem input_cacheSize (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) :
    (input δ k runs pages).cacheSize = k := rfl

@[simp] theorem input_length (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) :
    (input δ k runs pages).requests.length = runLength k * runs := by
  simp [input]

theorem input_chronological (δ : Cost) (k runs : ℕ) (pages : Fin (k + 2) ↪ Page) :
    (input δ k runs pages).Chronological := by
  show List.Pairwise _ ((List.range (runLength k * runs)).map (requestAt δ k runs pages))
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp fun {m m'} h => arrivalTime_mono k h.le

theorem input_valid (δ : Cost) {k : ℕ} (runs : ℕ) (pages : Fin (k + 2) ↪ Page)
    (hk : 0 < k) : (input δ k runs pages).Valid where
  chronological := input_chronological δ k runs pages
  positiveCapacity := hk
  initialCache_nodup := initialCache_nodup k hk pages
  initialCache_full := initialCache_length k pages

end
end PagingWithDelay.LowerBound
