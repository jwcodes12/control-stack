import ControlStack.Scenarios.SC26Transaction

namespace ControlStack.SC26

def Back_sc26_once : Prop :=
  ∀ (R : Roles) (cap : ℕ) (ops : List Op),
    (run R cap full init ops).reserved.Nodup

end ControlStack.SC26
