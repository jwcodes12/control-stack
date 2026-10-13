import ControlStack.Scenarios.SC06Artifacts

namespace ControlStack.SC06

def Back_halt_freezes : Prop :=
  ∀ (P : Policy) (s : St) (ops : List Op),
    s.halted = true → run P full s ops = s

end ControlStack.SC06
