import ControlStack.Scenarios.SC15Review

namespace ControlStack.SC15

def Back_halt_freezes : Prop :=
  ∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true → run E full s ops = s

end ControlStack.SC15
