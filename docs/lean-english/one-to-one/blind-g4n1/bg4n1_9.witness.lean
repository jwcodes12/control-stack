theorem witness : Witness := by
  simp only [Witness, BackAt, ControlStack.SC18Liveness.Resume.RelOk]
  decide
