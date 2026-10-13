open ControlStack.SC23IsolationV2 ControlStack.Authenticated ControlStack.Gate
theorem claim : Claim := by
  exact ⟨rfl, fun _ _ _ _ _ _ _ _ => Iff.rfl⟩

theorem witness : Witness := by
  unfold Witness
  constructor
  · simp [E0]
  · decide
