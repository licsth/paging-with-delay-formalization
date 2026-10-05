import Model

/-!
# An equivalent form of `Algorithm.Online`

`Model.lean` defines onlineness by comparing two instances that agree up to a
time.  `online_iff_upTo_eq` shows this is the same as the phrasing such an
algorithm is usually given: its behaviour up to `t` is unchanged if the request
sequence is truncated at `t`.  That form is what the FIFO proof uses.

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

/-- An online algorithm behaves, before time `t`, exactly as it would have on
the input truncated at `t`.  This is the usual informal reading of "does not
look into the future". -/
theorem Online.upTo_eq {algorithm : Algorithm Page} (online : Online algorithm)
    (input : Instance Page) (t : Time) :
    (algorithm input).upTo t = (algorithm (input.upTo t)).upTo t :=
  online.prefixDetermined input (input.upTo t) t
    (input.upTo_idem t).symm

/-- Conversely, an algorithm that cannot tell the full input from its
truncation is online, so the two phrasings agree. -/
theorem online_of_upTo_eq {algorithm : Algorithm Page}
    (h : ∀ (input : Instance Page) (t : Time),
      (algorithm input).upTo t = (algorithm (input.upTo t)).upTo t) :
    Online algorithm where
  prefixDetermined first second t heq := by
    rw [h first t, h second t, heq]

theorem online_iff_upTo_eq (algorithm : Algorithm Page) :
    Online algorithm ↔
      ∀ (input : Instance Page) (t : Time),
        (algorithm input).upTo t = (algorithm (input.upTo t)).upTo t :=
  ⟨fun online input t => online.upTo_eq input t,
    online_of_upTo_eq⟩

end Algorithm

end
end PagingWithDelay
