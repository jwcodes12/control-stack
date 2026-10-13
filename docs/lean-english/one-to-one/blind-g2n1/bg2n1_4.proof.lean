open ControlStack.SC09

theorem claim : Claim := by
  refine ⟨rfl, ?_, ?_⟩
  · intros
    exact Iff.rfl
  · intros
    constructor
    · intro h
      exact ⟨h.1, h.2⟩
    · intro h
      exact ⟨h.caps, h.uses⟩

theorem witness : Witness := by
  unfold Witness
  decide
