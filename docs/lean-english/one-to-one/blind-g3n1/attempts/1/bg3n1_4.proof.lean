theorem original_type : OrigClosed := @ControlStack.AuthInstances.forged15_merges_without_auth

theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_, ?_⟩
  · intro u c h
    obtain ⟨hu, hc⟩ := h
    exact ⟨by simp [hu], hc⟩
  · refine ⟨{ init with merged := [⟨0, 1, 999, [5], [5]⟩] }, init, ?_⟩
    decide
theorem witness : Witness := by
  refine ⟨by decide, by decide, ?_⟩
  intro u c h
  obtain ⟨hu, hc⟩ := h
  exact ⟨by simp [hu], hc⟩
