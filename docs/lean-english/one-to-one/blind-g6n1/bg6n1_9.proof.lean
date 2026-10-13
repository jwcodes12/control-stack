open ControlStack.SC25Refinement ControlStack.SC25

theorem claim : Claim := by
  constructor
  · rfl
  · intros; exact Iff.rfl

theorem witness : Witness := by
  unfold Witness
  refine ⟨fun _ _ _ _ he => he, ?_, ?_⟩ <;> decide
