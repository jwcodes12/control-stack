import ControlStack.Scenarios.SC08Exec

namespace ControlStack.SC08

def Back_sc08_halt_freezes : Prop :=
  ∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true → run E full s ops = s

end ControlStack.SC08
