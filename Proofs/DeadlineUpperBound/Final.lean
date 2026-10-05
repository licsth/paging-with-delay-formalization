import Proofs.KPlusOne.Final

/-!
# FIFO upper bounds for paging with deadlines

The write-up's Section "FIFO upper bounds for paging with deadlines".
Deadline-triggered FIFO (`FIFO.deadlineAlgorithm`) runs the same event loop as
threshold FIFO with a different trigger, so the payment windows, the rank
potential and the potential changes of `Proofs/RankPotential/` apply verbatim,
with `Setup.trigger = .deadline`.

The one new ingredient is that Case 3 cannot occur against a comparator meeting
every deadline (`neverSet_eq_empty`): one of the requests served at a payment
has its deadline at the payment, and in Case 3 the comparator serves it
strictly after it (`RankPotential.delay_pos_of_never`).
The combinatorial accounting `payment_accounting_nat_of_gain` then has no delay
term, which gives the deadline accounting `M + Φ_final - Φ_0 ≤ (k+1)·S`
(`deadline_accounting_missing`), and `M + Φ_final - Φ_0 ≤ k·S` on `k+1` pages
(`deadline_accounting_missing_k_plus_one`).  With `ALG = M` and `S ≤ OPT`,
deadline-triggered FIFO is strictly `(k+1)`-competitive (`strictlyCompetitive`),
and strictly `k`-competitive on `k+1` pages
(`strictlyCompetitive_k_plus_one`).
-/

namespace PagingWithDelay.DeadlineUpperBound

open PagingWithDelay Analysis RankPotential

variable {Page : Type*} [DecidableEq Page]

noncomputable section

section Accounting

variable {S : Setup Page} {comparator : Schedule Page}

/-- **Case 3 cannot occur** against a comparator meeting every deadline. -/
theorem neverSet_eq_empty (hdeadline : S.trigger = .deadline) (feasible : comparator.Feasible S.input)
    (meets : ∀ request ∈ S.input.requests, comparator.requestCost request = 0) :
    neverSet S comparator = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun i hmem => ?_
  simp only [neverSet, Finset.mem_filter, Finset.mem_range] at hmem
  obtain ⟨hi, hnever⟩ := hmem
  have hzero : ((S.payments[i]).served.map fun occurrence =>
      comparator.requestCost occurrence.request).sum = 0 := by
    refine List.sum_eq_zero fun cost hcost => ?_
    obtain ⟨occurrence, ho, rfl⟩ := List.mem_map.mp hcost
    exact meets _ (S.served_request_mem hi ho)
  exact (delay_pos_of_never hdeadline feasible hi hnever).ne' hzero

/-- **Deadline accounting with a general fetch charge**, in the write-up's
potential: `M + Φ_final ≤ c·S + Φ_0` whenever every associated offline event
has gain at least `g = 2k+1-c`. -/
theorem deadline_accounting_missing_of_gain (hdeadline : S.trigger = .deadline)
    (feasible : comparator.Feasible S.input)
    (meets : ∀ request ∈ S.input.requests, comparator.requestCost request = 0)
    {c g : ℕ} (hcg : c + g = 2 * S.cacheSize + 1) (hgk : g ≤ S.cacheSize + 1)
    (hg : ∀ i, i < S.count → Dropped S comparator i →
      g ≤ gainAt S comparator (assoc S comparator i).1 (assoc S comparator i).2) :
    S.count + missing S comparator S.count ≤
      c * comparator.fetchCount + missing S comparator 0 := by
  have h := payment_accounting_nat_of_gain feasible hcg hgk hg
  rw [neverSet_eq_empty hdeadline feasible meets, Finset.card_empty, mul_zero, add_zero] at h
  have hE : c * eventIndex S comparator S.count ≤ c * comparator.fetchCount :=
    Nat.mul_le_mul_left _ (eventIndex_le_length S.count)
  have e1 := missing_add_potential (S := S) (comparator := comparator) le_rfl
  have e0 := missing_add_potential (S := S) (comparator := comparator) (Nat.zero_le _)
  omega

/-- **Deadline accounting** in the write-up's form:
`M + Φ_final - Φ_0 ≤ (k+1)·S`, stated additively, with
`Φ = ∑_{q ∈ C_ALG \ C_OPT} rank q` read as in
`RankPotential.payment_accounting_missing`. -/
theorem deadline_accounting_missing (hdeadline : S.trigger = .deadline)
    (feasible : comparator.Feasible S.input)
    (meets : ∀ request ∈ S.input.requests, comparator.requestCost request = 0) :
    S.count + missing S comparator S.count ≤
      (S.cacheSize + 1) * comparator.fetchCount + missing S comparator 0 :=
  deadline_accounting_missing_of_gain hdeadline feasible meets (c := S.cacheSize + 1) (g := S.cacheSize)
    (by ring) (Nat.le_succ _) (fun _ hi h => gain_assoc_ge hi h)

/-- **Deadline accounting on `k+1` pages**: `M + Φ_final - Φ_0 ≤ k·S`. -/
theorem deadline_accounting_missing_k_plus_one (hdeadline : S.trigger = .deadline)
    (feasible : comparator.Feasible S.input)
    (meets : ∀ request ∈ S.input.requests, comparator.requestCost request = 0)
    (huniverse : S.input.pageUniverse.card ≤ S.cacheSize + 1) :
    S.count + missing S comparator S.count ≤
      S.cacheSize * comparator.fetchCount + missing S comparator 0 :=
  deadline_accounting_missing_of_gain hdeadline feasible meets (c := S.cacheSize) (g := S.cacheSize + 1)
    (by ring) le_rfl (fun _ hi h => KPlusOne.gain_assoc_ge_succ huniverse hi h)

/-- `M ≤ (k+1)·S` against a comparator meeting every deadline. -/
theorem paymentCount_le (hdeadline : S.trigger = .deadline) (feasible : comparator.Feasible S.input)
    (meets : ∀ request ∈ S.input.requests, comparator.requestCost request = 0) :
    S.count ≤ (S.cacheSize + 1) * comparator.fetchCount := by
  have h := deadline_accounting_missing hdeadline feasible meets
  rw [missing_zero feasible] at h
  omega

/-- `M ≤ k·S` on `k+1` pages, against a comparator meeting every deadline. -/
theorem paymentCount_le_k_plus_one (hdeadline : S.trigger = .deadline)
    (feasible : comparator.Feasible S.input)
    (meets : ∀ request ∈ S.input.requests, comparator.requestCost request = 0)
    (huniverse : S.input.pageUniverse.card ≤ S.cacheSize + 1) :
    S.count ≤ S.cacheSize * comparator.fetchCount := by
  have h := deadline_accounting_missing_k_plus_one hdeadline feasible meets huniverse
  rw [missing_zero feasible] at h
  omega

end Accounting

/-! ### The theorems -/

/-- The setup of deadline-triggered FIFO on an instance. -/
def setupDeadline (input : Instance Page) : Setup Page where
  cacheSize := input.cacheSize
  positive := input.positiveCapacity
  trigger := .deadline
  input := input
  size := rfl

/-- `ALG = M`: a deadline payment costs one fetch and no delay. -/
theorem totalCost_eq (input : Instance Page) :
    (FIFO.schedule .deadline input).totalCost input = (setupDeadline input).count := by
  have hcost := FIFO.algorithmCostClaim .deadline input
  unfold FIFO.AlgorithmCostClaim FIFO.algorithmCost at hcost
  rw [hcost, FIFO.Trigger.level_deadline, add_zero, one_mul]
  rfl

/-- `ALG ≤ ratio · S ≤ ratio · OPT` from a bound `M ≤ ratio · S`. -/
private theorem totalCost_le_of_count_le {input : Instance Page} {comparator : Schedule Page}
    {ratio : ℕ} (h : (setupDeadline input).count ≤ ratio * comparator.fetchCount) :
    (FIFO.schedule .deadline input).totalCost input ≤ (ratio : Cost) * comparator.totalCost input := by
  rw [totalCost_eq]
  calc ((setupDeadline input).count : Cost)
      ≤ ((ratio * comparator.fetchCount : ℕ) : Cost) := by exact_mod_cast h
    _ = (ratio : Cost) * comparator.fetchCount := by push_cast; ring
    _ ≤ (ratio : Cost) * comparator.totalCost input := by
        gcongr
        exact le_self_add

/-- **Deadline-triggered FIFO is strictly `(k+1)`-competitive** against every
feasible comparator schedule meeting every deadline. -/
theorem competitiveRatio (input : Instance Page) (comparator : Schedule Page)
    (feasible : comparator.Feasible input)
    (meets : ∀ request ∈ input.requests, comparator.requestCost request = 0) :
    (FIFO.schedule .deadline input).totalCost input ≤
      (input.cacheSize + 1 : ℕ) * comparator.totalCost input :=
  totalCost_le_of_count_le (paymentCount_le (S := setupDeadline input) rfl feasible meets)

/-- **On `k+1` pages, deadline-triggered FIFO is strictly `k`-competitive**
against every feasible comparator schedule meeting every deadline. -/
theorem competitiveRatio_k_plus_one (input : Instance Page)
    (huniverse : input.pageUniverse.card ≤ input.cacheSize + 1)
    (comparator : Schedule Page) (feasible : comparator.Feasible input)
    (meets : ∀ request ∈ input.requests, comparator.requestCost request = 0) :
    (FIFO.schedule .deadline input).totalCost input ≤ (input.cacheSize : ℕ) * comparator.totalCost input :=
  totalCost_le_of_count_le
    (paymentCount_le_k_plus_one (S := setupDeadline input) rfl feasible meets huniverse)

/-- **The `k+1` theorem** in the form `PagingWithDelay.lean` states it. -/
theorem strictlyCompetitive :
    (FIFO.deadlineAlgorithm (Page := Page)).StrictlyCompetitive fun k => k + 1 :=
  DeadlineAlgorithm.strictlyCompetitive_of_schedules fun input _ comparator feasible meets => by
    simpa using competitiveRatio input comparator feasible meets

/-- **The `k`-on-`k+1`-pages theorem** in the form `PagingWithDelay.lean` states it. -/
theorem strictlyCompetitive_k_plus_one :
    (FIFO.deadlineAlgorithm (Page := Page)).StrictlyCompetitive (fun k => k)
      fun input => input.pageUniverse.card ≤ input.cacheSize + 1 :=
  DeadlineAlgorithm.strictlyCompetitive_of_schedules fun input huniverse comparator feasible meets =>
    competitiveRatio_k_plus_one input huniverse comparator feasible meets

end

end PagingWithDelay.DeadlineUpperBound
