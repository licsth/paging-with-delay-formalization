import PagingWithDelay.Model
import PagingWithDelay.Analysis.Amortized

/-!
# Delay accrued so far

A delay cost is paid once, when the request is finally served, but an
amortized argument needs to spend it as it accumulates.  `accruedCost` is the
delay a schedule has accumulated on a request by time `t`: the request waits
until it is served, or until `t` if it is still pending then.

The two facts an interval argument needs are here: the accrual is monotone in
`t` and never exceeds the delay actually charged (`accruedCost_le_requestCost`),
so the increments over a chain of times sum to at most the total delay
(`sum_delayIncrement_le`).

This is generic online-with-delay machinery: it mentions no algorithm.
-/

namespace PagingWithDelay.Analysis

open PagingWithDelay

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- Delay accrued by `schedule` on `request` up to time `t`. -/
def accruedCost (schedule : Schedule Page) (request : Request Page) (t : Time) : Cost :=
  request.delay (min ((schedule.serviceTime request).getD t) t - request.arrival)

theorem accruedCost_mono (schedule : Schedule Page) (request : Request Page) :
    Monotone (accruedCost schedule request) := by
  intro s t hst
  apply request.delay_mono
  apply tsub_le_tsub_right
  cases hservice : schedule.serviceTime request with
  | none => simp only [Option.getD_none, min_self]; exact hst
  | some time =>
      simp only [Option.getD_some]
      exact min_le_min (le_refl time) hst

theorem accruedCost_eq_zero {schedule : Schedule Page} {request : Request Page} {t : Time}
    (ht : t ≤ request.arrival) : accruedCost schedule request t = 0 := by
  have : min ((schedule.serviceTime request).getD t) t - request.arrival = 0 := by
    apply tsub_eq_zero_of_le
    exact (min_le_right _ _).trans ht
  rw [accruedCost, this, request.delay_zero]

/-- If the schedule has no service candidate before `t`, the request has been
waiting for the whole time `t - arrival`. -/
theorem accruedCost_eq_of_le_serviceTime {schedule : Schedule Page} {request : Request Page}
    {t : Time} (h : ∀ time ∈ schedule.serviceTime request, t ≤ time) :
    accruedCost schedule request t = request.delay (t - request.arrival) := by
  unfold accruedCost
  congr 1
  cases hservice : schedule.serviceTime request with
  | none => simp only [Option.getD_none, min_self]
  | some time =>
      have hle : t ≤ time := h time (by rw [hservice]; rfl)
      simp only [Option.getD_some, min_eq_right hle]

theorem accruedCost_le_requestCost {schedule : Schedule Page} {request : Request Page}
    (hserved : (schedule.serviceCandidates request).Nonempty) (t : Time) :
    accruedCost schedule request t ≤ schedule.requestCost request := by
  have hservice : schedule.serviceTime request =
      some ((schedule.serviceCandidates request).min' hserved) := by
    simp [Schedule.serviceTime, hserved]
  unfold accruedCost Schedule.requestCost Schedule.serviceDelay
  rw [hservice]
  apply request.delay_mono
  simp only [Option.getD_some]
  exact tsub_le_tsub_right (min_le_left _ t) _

/-- Accrual of the `n`-th request of the instance, `0` past its end. -/
def accruedAt (schedule : Schedule Page) (input : Instance Page) (n : ℕ) (t : Time) : Cost :=
  (input.requests[n]?).elim 0 fun request => accruedCost schedule request t

theorem accruedAt_mono (schedule : Schedule Page) (input : Instance Page) (n : ℕ) :
    Monotone (accruedAt schedule input n) := by
  intro s t hst
  unfold accruedAt
  cases hrequest : input.requests[n]? with
  | none => simp only [Option.elim_none]; exact le_rfl
  | some request => simp only [Option.elim_some]; exact accruedCost_mono schedule request hst

theorem accruedAt_le_requestCost {schedule : Schedule Page} {input : Instance Page}
    (feasible : schedule.Feasible input) (n : ℕ) (t : Time) :
    accruedAt schedule input n t ≤
      (input.requests[n]?).elim 0 schedule.requestCost := by
  unfold accruedAt
  cases hrequest : input.requests[n]? with
  | none => simp only [Option.elim_none]; exact le_rfl
  | some request =>
      have hmem : request ∈ input.requests := List.mem_of_getElem? hrequest
      simp only [Option.elim_some]
      exact accruedCost_le_requestCost (feasible.eventuallyServed request hmem) t

omit [DecidableEq Page] in
theorem sum_range_getElem?_elim (l : List (Request Page)) (f : Request Page → Cost) :
    ∑ n ∈ Finset.range l.length, (l[n]?).elim 0 f = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons request rest ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.elim_some]
      rw [ih, List.map_cons, List.sum_cons, add_comm]

/-- The delay accrued between two times, summed over all requests. -/
def delayIncrement (schedule : Schedule Page) (input : Instance Page) (s t : Time) : Cost :=
  ∑ n ∈ Finset.range input.requests.length,
    (accruedAt schedule input n t - accruedAt schedule input n s)

/-- Any set of requests charged over an interval charges at most the interval's
total delay increment. -/
theorem sum_le_delayIncrement (schedule : Schedule Page) (input : Instance Page)
    (s t : Time) {ids : Finset ℕ} (hids : ids ⊆ Finset.range input.requests.length) :
    ∑ n ∈ ids, (accruedAt schedule input n t - accruedAt schedule input n s) ≤
      delayIncrement schedule input s t :=
  Finset.sum_le_sum_of_subset hids

/-- Delay increments over a chain of times never overspend the total delay. -/
theorem sum_delayIncrement_le {schedule : Schedule Page} {input : Instance Page}
    (feasible : schedule.Feasible input) (time : ℕ → Time) (hmono : Monotone time)
    {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, delayIncrement schedule input (time i) (time (i + 1)) ≤
      schedule.totalDelay input := by
  unfold delayIncrement
  rw [Finset.sum_comm]
  calc
    ∑ n ∈ Finset.range input.requests.length, ∑ i ∈ Finset.Ico a b,
        (accruedAt schedule input n (time (i + 1)) - accruedAt schedule input n (time i))
        ≤ ∑ n ∈ Finset.range input.requests.length,
          (input.requests[n]?).elim 0 schedule.requestCost := by
          refine Finset.sum_le_sum fun n _ => ?_
          have hmono' : Monotone fun i => accruedAt schedule input n (time i) :=
            (accruedAt_mono schedule input n).comp hmono
          exact (Analysis.sum_Ico_increment_le hmono' hab).trans
            (accruedAt_le_requestCost feasible n (time b))
    _ = schedule.totalDelay input := sum_range_getElem?_elim _ _

end
end PagingWithDelay.Analysis
