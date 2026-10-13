open ControlStack.SC27Chain


theorem claim : Claim := by
  constructor
  · exact Iff.rfl
  · intros
    exact Iff.rfl

theorem witness : Witness := by
  unfold Witness
  decide
