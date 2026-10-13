open ControlStack
open ControlStack.SC15 ControlStack.AuthInstances ControlStack.AuthenticatedLog

theorem original_type : OrigClosed := @ControlStack.AuthInstances.forged15_merges_without_auth

theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_, ?_⟩
  · intro u c h
    obtain ⟨hu, hc⟩ := h
    exact ⟨by simp [hu], hc⟩
  · refine ⟨{ init with merged := [⟨0, 1, 999, [5], [5]⟩] }, init, ?_⟩
    unfold BackAt OrigAt
    decide
theorem witness : Witness := by
  unfold Witness
  refine ⟨by unfold OrigAt; decide, by decide, ?_⟩
  intro u c h
  obtain ⟨hu, hc⟩ := h
  exact ⟨by simp [hu], hc⟩
