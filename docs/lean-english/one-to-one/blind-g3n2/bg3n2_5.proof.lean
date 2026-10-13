open ControlStack
open ControlStack.SC17

theorem claim : Claim := ⟨Iff.rfl, fun _ _ _ => Iff.rfl⟩

theorem witness : Witness := by
  unfold Witness BackAt
  decide
