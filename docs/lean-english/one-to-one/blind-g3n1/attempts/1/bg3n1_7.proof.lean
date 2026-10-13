theorem original_type : OrigClosed := @ControlStack.SC16.halt_freezes

theorem claim : Claim := ⟨Iff.rfl, Iff.rfl, fun _ _ _ _ _ => Iff.rfl⟩
theorem witness : Witness := by decide
