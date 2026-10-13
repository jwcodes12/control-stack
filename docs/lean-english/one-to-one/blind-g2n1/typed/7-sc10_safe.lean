import ControlStack.Scenarios.SC10Policy

namespace ControlStack.SC10

def Back_sc10_safe : Prop :=
  ∀ (E : Env), E.h E.pinned = E.pinnedDigest →
    ∀ (ops : List Op), Good E (run E full init ops)

end ControlStack.SC10
