open ControlStack.SC27Refinement
open ControlStack.SC27ExtensionOnly (Env)

theorem claim : Claim := by
  constructor
  · exact Iff.rfl
  · intros
    exact Iff.rfl

theorem witness : Witness := by
  dsimp only [Witness]
  refine ⟨?_, ?_, by decide⟩
  · simp [TraceInj, ExamInj, stepC, examine, cinit, anchorIt, Set.InjOn]
  · exact ⟨(6, [5]), by decide, rfl⟩
