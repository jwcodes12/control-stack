open ControlStack.SC23Isolation
theorem claim : Claim := by
  exact ⟨rfl, fun _ _ _ _ => Iff.rfl⟩

theorem basicWitness : BasicWitness := by
  unfold BasicWitness
  constructor
  · repeat' constructor
  · decide


theorem witness : Witness := by
  refine ⟨basicWitness, ?_⟩
  unfold LimitWitness
  refine ⟨?_, ?_, ?_⟩
  · repeat' constructor
  · decide
  · decide
