open ControlStack.SC12

theorem claim : Claim := by
  refine ⟨rfl, ?_, ?_⟩
  · intros
    exact Iff.rfl
  · intros
    exact Iff.rfl

theorem witness : Witness := by
  unfold Witness
  decide
