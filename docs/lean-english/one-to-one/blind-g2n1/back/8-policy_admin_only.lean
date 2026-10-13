import ControlStack.Scenarios.SC10Policy

namespace ControlStack.SC10

def Back_policy_admin_only : Prop :=
  ∀ (E : Env), E.h E.pinned = E.pinnedDigest →
    ∀ (ops : List Op),
      ∀ pv ∈ (run E full init ops).versions, pv.2 ∈ E.admins

end ControlStack.SC10
