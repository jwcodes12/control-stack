import ControlStack.Scenarios.SC19Prod

namespace ControlStack.SC19

def Back_sc19_halt_freezes : Prop :=
  ∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true →
    run E full s ops = s

end ControlStack.SC19
