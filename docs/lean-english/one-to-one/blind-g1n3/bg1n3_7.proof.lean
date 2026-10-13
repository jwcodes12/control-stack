open ControlStack.SC07Refinement

theorem original_signature : ∀ (K : CCfg) (ops : List COp) (w : ℕ), K.quotaRule = true → 0 < K.Q → OriginalAt K ops w := by
  intro K ops w hK hQ
  exact concrete_wire_lt K hK hQ ops w

theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_⟩
  intro K ops w hK hQ
  rfl

theorem witness : Witness := by unfold Witness; decide
