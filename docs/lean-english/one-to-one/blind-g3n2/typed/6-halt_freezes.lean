import ControlStack.Scenarios.SC17Infra

namespace ControlStack.SC17

-- Only the applied log is asserted to remain unchanged after halt.
def Back_halt_freezes : Prop :=
  ∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true → (run E full s ops).applied = s.applied

end ControlStack.SC17
