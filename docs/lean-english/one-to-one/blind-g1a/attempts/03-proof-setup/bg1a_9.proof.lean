open ControlStack.SC07Refinement

theorem claim : Claim := by
  have originalSignature : ∀ (K : CCfg) (ops : List COp) (_hK : K.quotaRule = true), OrigAt K ops := fun K ops hK => ControlStack.SC07Refinement.concrete_safe K hK ops
  exact ⟨rfl, by intros; exact Iff.rfl⟩

theorem witness : Witness := by
  decide
