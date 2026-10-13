open ControlStack.SC27ExtensionOnly


theorem claim : Claim := by
  constructor
  · exact Iff.rfl
  · intros
    exact Iff.rfl

theorem witness : Witness := by
  dsimp only [Witness]
  refine ⟨run_inv E0 init _ (inv_init E0), ?_, by decide⟩
  exact ⟨(6, [5]), by decide, rfl⟩
