open ControlStack.SC23IsolationV2 ControlStack.Authenticated ControlStack.Gate
theorem claim : Claim := by
  exact ⟨rfl, fun _ _ _ _ => Iff.rfl⟩

theorem witness : Witness := by
  unfold Witness
  constructor
  · apply List.Forall₂.cons ⟨rfl, Or.inr ⟨66,0,rfl,rfl⟩⟩
    apply List.Forall₂.cons ⟨rfl, Or.inl rfl⟩
    apply List.Forall₂.cons ⟨rfl, Or.inl rfl⟩
    exact List.Forall₂.nil
  · decide
