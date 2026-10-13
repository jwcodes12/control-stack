open ControlStack.SC25

theorem claim : Claim := by
  constructor
  · rfl
  · intros; exact Iff.rfl

theorem witness : Witness := by
  unfold Witness
  decide
