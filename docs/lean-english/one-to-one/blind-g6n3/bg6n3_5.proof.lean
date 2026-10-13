open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26Liveness ControlStack.SC26Liveness.Concrete ControlStack.SC26LossyLiveness ControlStack.SC26LossyHalt

theorem runners (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) :
    runLH R cap true s ops = runL R cap true s ops := by
  have hs : stepLH R cap true = stepL R cap true := by
    funext s o
    cases o <;> rfl
  simp only [runLH, runL, hs]

theorem pointwise : Pointwise := by
  intro R cap s ops k _ _
  unfold BackAt OrigAt
  rw [runners]


theorem witness : Witness := by
  refine ⟨rfl, rfl, by decide, ?_, by decide⟩
  simp [trace, legalL, legalC]


theorem claim : Claim := ⟨pointwise, Iff.rfl, Iff.rfl⟩
