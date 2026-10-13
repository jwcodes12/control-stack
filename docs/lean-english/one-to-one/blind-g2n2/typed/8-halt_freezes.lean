import ControlStack.Scenarios.SC14Runaway

namespace ControlStack.SC14

def Back_halt_freezes : Prop :=
  ∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true → (run E full s ops).usage = s.usage

end ControlStack.SC14
