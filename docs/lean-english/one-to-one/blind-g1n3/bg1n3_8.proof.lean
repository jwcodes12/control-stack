open ControlStack.SC07Refinement

theorem original_signature : ∀ (K : CCfg) (pre post : List COp), K.quotaRule = true → (runC K cinit pre).halted = true → OriginalAt K pre post := by
  intro K pre post hK hh
  exact concrete_halt_freezes K hK pre post hh

theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_⟩
  intro K pre post hK hh
  rfl

theorem witness : Witness := by unfold Witness; decide
