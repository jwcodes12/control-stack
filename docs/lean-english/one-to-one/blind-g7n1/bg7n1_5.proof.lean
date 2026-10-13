open ControlStack.SC27ExtensionOnly
open ControlStack.SC27Chain (chainHead)

theorem claim : Claim := by
  constructor
  · exact Iff.rfl
  · intros
    exact Iff.rfl

theorem witness : Witness := by
  dsimp only [Witness]
  have ha : (run E0 true init [.append 5, .anchor, .verify [5]]).accepted = [[5]] := by decide
  have hb : (run E0 true init [.append 5, .anchor, .verify [5]]).anchors = [(6, [5])] := by decide
  refine ⟨ha, hb, by decide, ?_, by decide⟩
  rw [ha, hb]
  simp [Set.InjOn]
