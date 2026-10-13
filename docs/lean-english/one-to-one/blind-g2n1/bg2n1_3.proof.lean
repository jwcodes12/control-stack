open ControlStack.SC08

theorem claim : Claim := by
  refine ⟨rfl, ?_⟩
  intros
  exact Iff.rfl

theorem witness : Witness := by
  unfold Witness
  decide
