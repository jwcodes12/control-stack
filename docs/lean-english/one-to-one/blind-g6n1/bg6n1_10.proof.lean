open ControlStack.SC26

theorem claim : Claim := by
  constructor
  · rfl
  · intros; exact Iff.rfl

theorem witness : Witness := by
  unfold Witness
  constructor
  · simp [legal]
  · decide
