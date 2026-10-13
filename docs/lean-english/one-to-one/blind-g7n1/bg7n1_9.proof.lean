open ControlStack.SC27Refinement
open ControlStack.SC27Chain (chainHead)
open ControlStack.SC27ExtensionOnly (Env)

theorem claim : Claim := by
  constructor
  · exact Iff.rfl
  · intros
    exact Iff.rfl

theorem witness : Witness := by
  dsimp only [Witness]
  have ht : TraceInj E0 cinit [.append 5, .examine, .verify [5]] := by
    simp [TraceInj, ExamInj, stepC, cinit]
  have ha : (runC E0 false cinit [.append 5, .examine, .verify [5]]).accepted = [[5]] := by decide
  have hb : ancs (runC E0 false cinit [.append 5, .examine, .verify [5]]).wlog = [(6, [5])] := by decide
  refine ⟨ht, ha, hb, by decide, ?_, by decide⟩
  rw [ha, hb]
  simp [Set.InjOn]
