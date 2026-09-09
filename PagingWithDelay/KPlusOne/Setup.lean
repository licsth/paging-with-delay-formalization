import PagingWithDelay.Algorithm
import PagingWithDelay.EventLoop.FreshQueue
import PagingWithDelay.EventLoop.History
import PagingWithDelay.EventLoop.PaymentAccounting

/-!
# The `k+1`-page setting

Section 5 of `fifo-upper-bound.tex` studies FIFO with threshold `(k+1)/k` on a
universe of exactly `k+1` pages.  `Setup` bundles those hypotheses, and this
file derives the structure of the FIFO run under them: the cache before a
payment is the window of the last `k` fetched pages, those pages are pairwise
distinct, and therefore exactly one page of the universe is missing — the one
the payment fetches, which is the page evicted by the previous payment.

Everything is read off the event loop of `Algorithm.lean` through the
threshold-independent invariants in `EventLoop/`.
-/

namespace PagingWithDelay.KPlusOne

open PagingWithDelay

variable {Page : Type*} [DecidableEq Page]

/-- The hypotheses of the `k+1`-page theorem: a cache of size `k ≥ 1` and a
request sequence drawn from a universe of `k + 1` pages. -/
structure Setup (Page : Type*) [DecidableEq Page] where
  /-- The cache size `k`. -/
  cacheSize : ℕ
  positive : 0 < cacheSize
  /-- The page universe `V`, of size `k + 1`. -/
  pages : Finset Page
  card : pages.card = cacheSize + 1
  input : Instance Page
  valid : input.Valid
  size : input.cacheSize = cacheSize
  requestPages : ∀ request ∈ input.requests, request.page ∈ pages

namespace Setup

noncomputable section

variable (S : Setup Page)

/-- The threshold `δ = (k+1)/k` of the `k+1`-page algorithm. -/
def threshold : Cost := ((S.cacheSize : Cost) + 1) / (S.cacheSize : Cost)

theorem cacheSize_ne_zero : (S.cacheSize : Cost) ≠ 0 := by
  have h := S.positive
  exact Nat.cast_ne_zero.mpr (by omega)

theorem threshold_pos : 0 < S.threshold := by
  unfold threshold
  exact div_pos (by positivity) (lt_of_le_of_ne (zero_le _) (Ne.symm S.cacheSize_ne_zero))

/-- The threshold is chosen so that `k · δ = k + 1`. -/
theorem cacheSize_mul_threshold : (S.cacheSize : Cost) * S.threshold = (S.cacheSize : Cost) + 1 := by
  have h := S.cacheSize_ne_zero
  unfold threshold
  field_simp

theorem pages_nonempty : S.pages.Nonempty := by
  apply Finset.card_pos.mp
  rw [S.card]
  omega

/-- An arbitrary page of the universe, used only as a junk default. -/
def somePage : Page := S.pages_nonempty.choose

/-- The completed FIFO run at threshold `δ = (k+1)/k`. -/
def payments : List (FIFO.Payment Page) :=
  (FIFO.run S.threshold S.input (2 * S.input.requests.length)
    (FIFO.initialState S.input)).payments

/-- `M`, the number of payments. -/
def count : ℕ := S.payments.length

/-- The page fetched by payment `i`. -/
def pageAt (i : ℕ) : Page := ((S.payments[i]?).map FIFO.Payment.page).getD S.somePage

theorem pageAt_eq {i : ℕ} (hi : i < S.count) : S.pageAt i = S.payments[i].page := by
  unfold pageAt
  rw [List.getElem?_eq_getElem (by simpa [count] using hi)]
  rfl

/-- The time of payment `i`, clamped at the last payment so that it is
monotone as a function on all of `ℕ`. -/
def timeAt (i : ℕ) : Time :=
  ((S.payments[min i (S.count - 1)]?).map FIFO.Payment.time).getD 0

theorem timeAt_eq {i : ℕ} (hi : i < S.count) : S.timeAt i = S.payments[i].time := by
  unfold timeAt
  rw [min_eq_left (by omega), List.getElem?_eq_getElem hi]
  rfl

theorem payment_time_le {i j : ℕ} (hi : i < S.count) (hj : j < S.count) (hij : i ≤ j) :
    S.payments[i].time ≤ S.payments[j].time := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact List.pairwise_iff_getElem.mp
      (FIFO.final_payment_times_chronological (δ := S.threshold) S.input S.valid) i j hi hj hlt

theorem timeAt_mono : Monotone S.timeAt := by
  intro i j hij
  unfold timeAt
  rcases Nat.eq_zero_or_pos S.count with hzero | hpos
  · have : S.payments = [] := List.eq_nil_of_length_eq_zero hzero
    simp [this]
  · have hi : min i (S.count - 1) < S.count := by omega
    have hj : min j (S.count - 1) < S.count := by omega
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    simpa using S.payment_time_le hi hj (by omega)

end

end Setup

end PagingWithDelay.KPlusOne
