import Model

/-!
# Delay curves for the tightness construction

Every request of the adversarial instance uses the same shape of delay curve:
it rises linearly to the threshold `δ` over a prescribed wait `w`, stays at
`δ`, and then grows again with slope `η`.

The `η` tail is the paper's "unbounded afterwards".  It is forced by
`Request.delay_unbounded`, which forbids a curve that is eventually constant.

The tail has its own breakpoint `B`, placed past the end of the instance, so
the curve is *flat* at `δ` in between.  Everything either algorithm does
happens before `B`, so the tail contributes nothing to either cost and its
slope needs no tuning; it only has to exist.  (`Time` is `NNReal`, so `x - B`
is truncated at zero and the tail term really is `η * max (x - B) 0`.)
-/

namespace PagingWithDelay.LowerBound

noncomputable section

/-- `curve δ η w B` rises linearly to `δ` at wait `w`, stays there until `B`,
and then grows with slope `η`. -/
def curve (δ η w B : Cost) (x : Time) : Cost := δ * min (x / w) 1 + η * (x - B)

theorem curve_continuous (δ η w B : Cost) : Continuous (curve δ η w B) := by
  unfold curve; fun_prop

theorem curve_mono (δ η w B : Cost) : Monotone (curve δ η w B) := by
  intro x y hxy; unfold curve; gcongr

@[simp] theorem curve_zero (δ η w B : Cost) : curve δ η w B 0 = 0 := by
  simp [curve]

/-- The tail makes the curve unbounded, as `Request` requires. -/
theorem curve_unbounded (δ η w B : Cost) (hη : 0 < η) (bound : Cost) :
    ∃ x : Time, bound ≤ curve δ η w B x := by
  refine ⟨B + bound / η, le_trans ?_ le_add_self⟩
  rw [add_tsub_cancel_left]
  exact le_of_eq (by field_simp)

/-- On the plateau — from the wait `w` at which the threshold is reached until
the tail starts at `B` — the curve is exactly `δ`.  This is what the comparator
uses: it leaves one request per run pending, and pays `δ` for it, no matter how
long it waits, as long as it serves it before `B`. -/
theorem curve_eq_threshold (δ η w B : Cost) (hw : 0 < w) {x : Time}
    (hwx : w ≤ x) (hxB : x ≤ B) : curve δ η w B x = δ := by
  have hone : min (x / w) 1 = 1 := min_eq_right ((one_le_div hw).mpr hwx)
  rw [curve, hone, mul_one, tsub_eq_zero_of_le hxB, mul_zero, add_zero]

/-- Before `w` the curve is still below the threshold, so a threshold-`δ` event
loop does not pay early.  This needs `0 < δ`; at threshold `0` there is nothing
to wait for and the loop pays on arrival, which is why the lower bound excludes
that case. -/
theorem curve_lt_threshold (δ η w B : Cost) (hδ : 0 < δ) (hwB : w ≤ B)
    {x : Time} (hx : x < w) : curve δ η w B x < δ := by
  have hw : 0 < w := lt_of_le_of_lt (zero_le x) hx
  have hlt : x / w < 1 := (div_lt_one hw).mpr hx
  have hsub : x - B = 0 := tsub_eq_zero_of_le (hx.le.trans hwB)
  rw [curve, hsub, mul_zero, add_zero, min_eq_left hlt.le]
  exact mul_lt_of_lt_one_right hδ hlt

/-- The request `page` issued at `arrival`, whose delay reaches the threshold
`δ` exactly `w` later. -/
def request {Page : Type*} (page : Page) (arrival : Time) (δ η w B : Cost)
    (hη : 0 < η) : Request Page where
  page := page
  arrival := arrival
  delay := curve δ η w B
  delay_continuous := curve_continuous δ η w B
  delay_mono := curve_mono δ η w B
  delay_zero := curve_zero δ η w B
  delay_unbounded := curve_unbounded δ η w B hη

end
end PagingWithDelay.LowerBound
