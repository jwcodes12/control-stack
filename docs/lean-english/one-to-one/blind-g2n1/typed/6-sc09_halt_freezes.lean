import ControlStack.Scenarios.SC09Priv

namespace ControlStack.SC09

def Back_sc09_halt_freezes : Prop :=
  ∀ (P : Policy) (s : St) (ops : List Op),
    s.halted = true → run P full s ops = s

end ControlStack.SC09
