open ControlStack
open ControlStack.SC15

theorem original_type : OrigClosed := @ControlStack.SC15.sc15_safe

theorem claim : Claim := ⟨Iff.rfl, Iff.rfl, fun _ _ => Iff.rfl⟩
theorem witness : Witness := by
  unfold Witness
  decide
