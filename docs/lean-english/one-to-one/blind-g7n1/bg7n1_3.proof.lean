open ControlStack.SC27Chain


theorem claim : Claim := by
  constructor
  · exact Iff.rfl
  · exact Iff.rfl

theorem witness : Witness := by
  unfold Witness BackAt
  decide
