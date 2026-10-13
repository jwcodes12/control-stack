import ControlStack.Scenarios.SC06Artifacts

namespace ControlStack.SC06

def Back_sc06_safe : Prop :=
  ∀ (P : Policy) (ops : List Op),
    Good P (run P full init ops)

end ControlStack.SC06
