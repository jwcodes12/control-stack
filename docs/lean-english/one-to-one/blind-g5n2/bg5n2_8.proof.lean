open ControlStack ControlStack.AuthInstances ControlStack.AuthenticatedLog
theorem claim : Claim := by
  rfl

theorem witness : Witness := by
  unfold Witness
  constructor
  · rfl
  · unfold Back_forged23_acts_without_auth
    decide
