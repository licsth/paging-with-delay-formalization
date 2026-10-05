import Model

namespace PagingWithDelay.FIFO

open Set

/-- The first crossing of a continuous monotone nonnegative-real function
attains the threshold.  This is the analytic core used by `thresholdTime`. -/
theorem value_at_sInf_first_crossing
    (f : NNReal → NNReal) (now threshold : NNReal)
    (hf : Continuous f) (hmono : Monotone f)
    (hnow : f now ≤ threshold)
    (hex : ∃ t, now ≤ t ∧ threshold ≤ f t) :
    f (sInf {t | now ≤ t ∧ threshold ≤ f t}) = threshold := by
  let S : Set NNReal := {t | now ≤ t ∧ threshold ≤ f t}
  have hS_nonempty : S.Nonempty := by
    simpa [S] using hex
  have hS_bdd : BddBelow S := ⟨0, fun _ _ => bot_le⟩
  have hS_closed : IsClosed S := by
    simpa [S] using isClosed_Ici.inter (isClosed_Ici.preimage hf)
  have hsInf_mem : sInf S ∈ S := hS_closed.csInf_mem hS_nonempty hS_bdd
  apply le_antisymm
  · obtain ⟨upper, hnow_upper, hthreshold_upper⟩ := hex
    have hthreshold_mem : threshold ∈ f '' Icc now upper :=
      intermediate_value_Icc hnow_upper hf.continuousOn ⟨hnow, hthreshold_upper⟩
    obtain ⟨root, hroot_interval, hroot_value⟩ := hthreshold_mem
    have hrootS : root ∈ S := ⟨hroot_interval.1, by simp [hroot_value]⟩
    have hsInf_le_root : sInf S ≤ root := csInf_le hS_bdd hrootS
    calc
      f (sInf S) ≤ f root := hmono hsInf_le_root
      _ = threshold := hroot_value
  · exact hsInf_mem.2

/-- Unboundedness supplies the nonempty crossing set needed by
`value_at_sInf_first_crossing`. -/
theorem value_at_sInf_first_crossing_of_unbounded
    (f : NNReal → NNReal) (now threshold : NNReal)
    (hf : Continuous f) (hmono : Monotone f)
    (hnow : f now ≤ threshold)
    (hunbounded : ∀ bound, ∃ t, bound ≤ f t) :
    f (sInf {t | now ≤ t ∧ threshold ≤ f t}) = threshold := by
  apply value_at_sInf_first_crossing f now threshold hf hmono hnow
  obtain ⟨t, ht⟩ := hunbounded threshold
  refine ⟨max now t, le_max_left _ _, ?_⟩
  exact ht.trans (hmono (le_max_right _ _))

end PagingWithDelay.FIFO
