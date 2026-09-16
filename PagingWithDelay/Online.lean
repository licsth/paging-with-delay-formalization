import PagingWithDelay.Model

/-!
# An equivalent form of `Algorithm.Online`

`Model.lean` defines onlineness by comparing two instances that agree up to a
time.  `online_iff_upTo_eq` shows this is the same as the phrasing such an
algorithm is usually given: its behaviour up to `t` is unchanged if the request
sequence is truncated at `t`.  That form is what the FIFO proof uses.

Witnesses that the definition is neither vacuously true nor vacuously false are
in `PagingWithDelay/OnlineExamples.lean`.
-/

namespace PagingWithDelay

noncomputable section

variable {Page : Type*}

/-- Truncating twice at the same time changes nothing. -/
@[simp] theorem Instance.upTo_idem (input : Instance Page) (t : Time) :
    (input.upTo t).upTo t = input.upTo t := by
  simp [Instance.upTo, List.filter_filter]

/-- A truncated instance is still a legal input: dropping requests preserves
chronology, and the cache capacity and initial cache are untouched. -/
theorem Instance.Valid.upTo {input : Instance Page} (valid : input.Valid) (t : Time) :
    (input.upTo t).Valid where
  chronological :=
    List.Pairwise.sublist List.filter_sublist valid.chronological
  positiveCapacity := valid.positiveCapacity
  initialCache_nodup := valid.initialCache_nodup
  initialCache_full := valid.initialCache_full

variable [DecidableEq Page]

namespace Algorithm

/-- An online algorithm behaves, before time `t`, exactly as it would have on
the input truncated at `t`.  This is the usual informal reading of "does not
look into the future". -/
theorem Online.upTo_eq {algorithm : Algorithm Page} (online : Online algorithm)
    (input : Instance Page) (valid : input.Valid) (t : Time)
    (validUpTo : (input.upTo t).Valid) :
    (algorithm input valid).upTo t = (algorithm (input.upTo t) validUpTo).upTo t :=
  online.prefixDetermined input (input.upTo t) valid validUpTo t
    (input.upTo_idem t).symm

/-- Conversely, an algorithm that cannot tell the full input from its
truncation is online, so the two phrasings agree. -/
theorem online_of_upTo_eq {algorithm : Algorithm Page}
    (h : ∀ (input : Instance Page) (valid : input.Valid) (t : Time)
      (validUpTo : (input.upTo t).Valid),
      (algorithm input valid).upTo t = (algorithm (input.upTo t) validUpTo).upTo t) :
    Online algorithm where
  prefixDetermined first second hfirst hsecond t heq := by
    have transport : ∀ (left right : Instance Page) (hleft : left.Valid)
        (hright : right.Valid), left = right → algorithm left hleft = algorithm right hright := by
      rintro left right hleft hright rfl
      rfl
    rw [h first hfirst t (hfirst.upTo t), h second hsecond t (hsecond.upTo t),
      transport _ _ (hfirst.upTo t) (hsecond.upTo t) heq]

theorem online_iff_upTo_eq (algorithm : Algorithm Page) :
    Online algorithm ↔
      ∀ (input : Instance Page) (valid : input.Valid) (t : Time)
        (validUpTo : (input.upTo t).Valid),
        (algorithm input valid).upTo t = (algorithm (input.upTo t) validUpTo).upTo t :=
  ⟨fun online input valid t validUpTo => online.upTo_eq input valid t validUpTo,
    online_of_upTo_eq⟩

end Algorithm

end
end PagingWithDelay
