open ControlStack.SC23Isolation
theorem claim : Claim := by
  exact ⟨rfl, fun _ _ _ _ => Iff.rfl⟩

theorem basicWitness : BasicWitness := by
  unfold BasicWitness
  decide


theorem witness : Witness := by
  refine ⟨basicWitness, ?_⟩
  unfold LimitWitness
  decide
