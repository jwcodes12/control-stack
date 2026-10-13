open ControlStack
open ControlStack.SC16

theorem original_type : OrigClosed := @ControlStack.SC16.sc16_safe

theorem claim : Claim := ⟨Iff.rfl, Iff.rfl, fun _ _ _ => Iff.rfl⟩
theorem witness : Witness := by
  unfold Witness
  decide
