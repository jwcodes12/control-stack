import ControlStack.Scenarios.SC10Policy

namespace ControlStack.SC10

def Back_sc10_halt_freezes : Prop :=
  ∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true → run E full s ops = s

end ControlStack.SC10
