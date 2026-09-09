import PagingWithDelay.LowerBound.CompCost

/-!
# The comparator for the adversarial instance

The offline solution of the TeX proof, and the cost it achieves.  The schedule
itself is built in `PagingWithDelay/LowerBound/CompSchedule.lean` and its cost
computed in `PagingWithDelay/LowerBound/CompCost.lean`; the statement below is
what the rest of the lower bound consumes.

## The intended schedule

The comparator's cache starts empty, as the model demands, so it first fetches
the `k` pages `v₁ … v_{k-1}, c` at time `0` — before the first arrival, which
is at `1/2`.  This is the additive `k` that the asymptotic statement absorbs;
the paper simply assumes the servers are already there.

Afterwards, per run:

* the request on `a` is left pending — the comparator never holds `a` — and
  pays the threshold `δ` plus a tail;
* at the arrival of the request on `b` (position `k+2`) the comparator fetches
  `b`, evicting `c`.  The repeat request on `c` (position `k+3`) has already
  been issued by then, and was served from cache at its own arrival, at no
  delay; the request on `b` is served by this fetch at no delay either.  This
  is the single fetch per run.
* every other request of the run is on `v₁ … v_{k-1}`, which the comparator
  holds throughout, and is served on arrival.

Runs alternate the roles of `b` and `c` (`swapBC`), so the same one-fetch
pattern repeats, and the comparator ends each run holding the page the next
run starts on.

Finally it fetches `a` once, which serves every request on `a` at once and
discharges `eventuallyServed`.  Those requests have then waited a long time,
but their curves are flat at `δ` until `horizon`, which the whole instance
fits inside, so each of them costs exactly `δ`.

Cost: `k` initial fetches, one fetch per run, one final fetch, and `δ` of delay
per run — exactly `(1 + δ) * runs + (k + 1)`.

In the formalization the `k` initial fetches are split as `k - 1` fetches of
`v₁ … v_{k-1}` (`initEvent`) plus the fetch of `c`, and that last one is
counted as the first of the `runs + 1` `phaseEvent`s: `phaseEvent r` is the
fetch that puts the comparator on `swapBC r 2`, so between `phaseEvent r` and
`phaseEvent (r+1)` its cache is the closed form `heldCache (swapBC r 2)`.
-/

namespace PagingWithDelay.LowerBound

variable {Page : Type*} [DecidableEq Page]

noncomputable section

/-- **The comparator of the paper.**  Cheap because it fetches once per run
and pays the threshold `δ` once per run, where FIFO fetches `2k+2` times and
pays `δ` that often. -/
theorem exists_comparator (δ : Cost) {k : ℕ} (runs : ℕ) (pages : Fin (k + 2) ↪ Page)
    (hk : 0 < k) :
    ∃ comparator : Schedule Page,
      comparator.Feasible (input δ k runs pages) ∧
        comparator.totalCost (input δ k runs pages) ≤ (1 + δ) * runs + (k + 1) :=
  ⟨comparator k runs pages, comparator_feasible hk pages,
    le_of_eq (comparator_totalCost hk pages)⟩

end
end PagingWithDelay.LowerBound
