open ControlStack
open ControlStack.SC15

theorem original_type : OrigClosed := @ControlStack.SC15.halt_freezes

theorem claim : Claim := ⟨Iff.rfl, Iff.rfl, fun _ _ _ _ => Iff.rfl⟩
theorem witness : Witness := by
  unfold Witness
  decide
