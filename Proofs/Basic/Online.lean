import Model

/-!
# An equivalent form of `Algorithm.Online`

`Model.lean` defines onlineness by comparing two instances that agree up to a
time.  `online_iff_upTo_eq` shows this is the same as the phrasing such an
algorithm is usually given: its behaviour up to `t` is unchanged if the request
sequence is truncated at `t`.

Witnesses that the definition is neither vacuously true nor vacuously false are
in `Checks/OnlineExamples.lean`.
-/

namespace PagingWithDelay

noncomputable section

variable {Page : Type*}

/-- Truncating twice at the same time changes nothing. -/
@[simp] theorem Instance.upTo_idem (input : Instance Page) (t : Time) :
    (input.upTo t).upTo t = input.upTo t := by
  simp [Instance.upTo, List.filter_filter]

variable [DecidableEq Page]

namespace Algorithm

/-- An algorithm is online exactly when its behaviour before time `t` is
unchanged if the input is truncated at `t`.  This is the usual informal reading
of "does not look into the future". -/
theorem online_iff_upTo_eq (algorithm : Algorithm Page) :
    Online algorithm ↔
      ∀ (input : Instance Page) (t : Time),
        (algorithm input).upTo t = (algorithm (input.upTo t)).upTo t :=
  ⟨fun online input t => online.prefixDetermined _ _ t (input.upTo_idem t).symm,
    fun h => ⟨fun first second t heq => by rw [h first t, h second t, heq]⟩⟩

end Algorithm

end
end PagingWithDelay
