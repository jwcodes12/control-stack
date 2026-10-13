import ControlStack.Scenarios.SC27Chain

namespace ControlStack.SC27Chain

def Back_halt_freezes : Prop :=
  ∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true → run E full s ops = s

end ControlStack.SC27Chain
