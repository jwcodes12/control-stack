theorem witness : Witness := by
  simp only [Witness, ControlStack.SC18Liveness.Resume.RelOk]
  decide
