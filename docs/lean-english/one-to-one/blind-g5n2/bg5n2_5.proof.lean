open ControlStack.SC23IsolationV2
theorem claim : Claim := by
  rfl

theorem witness : Witness := by
  unfold Witness
  decide
