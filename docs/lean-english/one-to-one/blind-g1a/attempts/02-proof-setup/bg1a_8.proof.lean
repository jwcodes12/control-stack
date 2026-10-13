theorem claim : Claim := by
  have originalSignature : ∀ (E : Env) (ops : List Op), OrigAt E ops := @ControlStack.SC07Liveness.sc07_safe
  exact ⟨rfl, by intros; exact Iff.rfl⟩

theorem witness : Witness := by
  decide
