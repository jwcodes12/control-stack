open ControlStack.TrustedBroker

theorem original_type : ∀ (roles : Roles) (s t : State), s.halted = true → Step roles s t →OrigConclusion roles s t := by
  intro roles s t hs ht
  exact ControlStack.TrustedBroker.halted_absorbing roles s t hs ht

theorem claim : Claim := by
  constructor
  · exact Iff.rfl
  · intro roles s t hs ht
    exact Iff.rfl

theorem witness : Witness := by exact ⟨rfl, .deny _, rfl⟩
