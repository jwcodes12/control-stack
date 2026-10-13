open ControlStack.SC20
theorem back_shape : Back_sc20_halt_freezes =
    (∀ E s ops, s.halted = true → BackPoint E s ops) := rfl
theorem original_type (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : OrigPoint E s ops := halt_freezes E s ops hh
theorem claim : Claim := by intro E s ops hh; exact Iff.rfl
theorem witness : Witness := by simp only [Witness]; decide
