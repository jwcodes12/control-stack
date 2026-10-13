open ControlStack.SC07Liveness

theorem original_signature :  OriginalAt := by
  exact shared_quota_blocks

theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_⟩
  rfl

theorem witness : Witness := by unfold Witness BackAt; decide
