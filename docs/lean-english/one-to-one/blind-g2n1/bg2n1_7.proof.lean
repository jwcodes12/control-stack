open ControlStack.SC10

theorem claim : Claim := by
  refine ⟨rfl, ?_, ?_⟩
  · intros
    exact Iff.rfl
  · intros
    constructor
    · intro h
      exact ⟨h.1, h.2⟩
    · intro h
      exact ⟨h.decs, h.builds⟩

theorem witness : Witness := by
  unfold Witness
  decide
