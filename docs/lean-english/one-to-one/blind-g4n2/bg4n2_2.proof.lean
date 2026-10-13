open ControlStack.SC18Refinement ControlStack.SC18Liveness
theorem back_shape : Back_concrete_durable = (∀ T ops, BackPoint T (runC real T cinit ops)) := rfl
theorem original_type (T : ℕ) (ops : List COp) : OrigPoint T (runC real T cinit ops) := concrete_durable T ops
theorem claim : Claim := by intro T s; exact Iff.rfl
theorem witness : Witness := by simp only [Witness]; decide
