import ControlStack.Scenarios.SC23Injection

namespace ControlStack.SC23

def Back_halt_freezes : Prop :=
  ∀ (P : Policy) (s : St) (ops : List Op),
    s.halted = true → run P full s ops = s

end ControlStack.SC23
