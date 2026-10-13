open ControlStack.SC27Chain

open ControlStack.SC27Chain (chainHead)

theorem claim : Claim := by
  constructor
  · exact Iff.rfl
  · intros
    exact Iff.rfl

theorem witness : Witness := by
  dsimp only [Witness]
  have ha : (run E0 full init [.append 5, .anchor, .verify [5]]).accepted = [[5]] := by decide
  have hb : (run E0 full init [.append 5, .anchor, .verify [5]]).anchors = [(6, some [5])] := by decide
  refine ⟨ha, hb, ?_, by decide, by decide⟩
  rw [ha, hb]
  simp [Set.InjOn]
