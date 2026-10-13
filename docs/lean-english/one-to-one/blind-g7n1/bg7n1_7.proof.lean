open ControlStack.SC27ExtensionOnly


theorem claim : Claim := by
  constructor
  · exact Iff.rfl
  · intros
    exact Iff.rfl

theorem witness : Witness := by
  unfold Witness
  decide
