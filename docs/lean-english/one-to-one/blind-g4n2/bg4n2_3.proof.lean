open ControlStack.SC19
theorem back_shape : Back_sc19_safe = (∀ E ops, BackPoint E (run E full init ops)) := rfl
theorem original_type (E : Env) (ops : List Op) : OrigPoint E (run E full init ops) := sc19_safe E ops
theorem claim : Claim := by intro E s; exact Iff.rfl
theorem witness : Witness := by simp only [Witness]; decide
