import ControlStack.Scenarios.SC09Priv

namespace ControlStack.SC09

def Back_sc09_safe : Prop :=
  ∀ (P : Policy) (ops : List Op),
    Good P (run P full init ops)

end ControlStack.SC09
