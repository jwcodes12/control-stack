import ControlStack.Scenarios.SC26Transaction

namespace ControlStack.SC26

def Back_sc26_safe : Prop :=
  ∀ (R : Roles) (cap : ℕ) (ops : List Op),
    (∀ o ∈ ops, legal R o) →
    Good R cap (run R cap full init ops)

end ControlStack.SC26
