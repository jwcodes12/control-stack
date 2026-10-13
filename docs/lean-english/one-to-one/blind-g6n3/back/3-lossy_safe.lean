import ControlStack.Scenarios.SC26LossyLiveness

namespace ControlStack.SC26LossyLiveness

open ControlStack.SC26 ControlStack.SC26Refinement

def Back_lossy_safe : Prop :=
  ∀ (R : Roles) (cap : ℕ) (ops : List LOp),
    (∀ o ∈ ops, legalL R o) →
    Good R cap (α (runL R cap true cinit ops))

end ControlStack.SC26LossyLiveness
