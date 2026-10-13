open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26Liveness ControlStack.SC26Liveness.Concrete ControlStack.SC26LossyLiveness ControlStack.SC26LossyHalt

theorem pointwise : Pointwise := by
  intro R cap ops _
  exact Iff.rfl


theorem witness : Witness := by
  refine ⟨?_, by decide, by decide⟩
  simp [trace, setupOps, legalL, legalC]


theorem claim : Claim := ⟨pointwise, Iff.rfl, Iff.rfl⟩
