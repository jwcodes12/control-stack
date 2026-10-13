theorem witness : Witness := by
  simp only [Witness, ControlStack.SC18.Good, ControlStack.SC18.RelOk]
  decide
