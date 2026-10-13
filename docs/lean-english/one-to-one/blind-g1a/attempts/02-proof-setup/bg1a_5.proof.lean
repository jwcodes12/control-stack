theorem claim : Claim := by
  have originalSignature : ∀ (forbidden : List ℕ) (ops : List Op), OrigAt forbidden ops := @ControlStack.SC05.forbidden_never_executes
  exact ⟨rfl, by intros; exact Iff.rfl⟩

theorem witness : Witness := by
  decide
