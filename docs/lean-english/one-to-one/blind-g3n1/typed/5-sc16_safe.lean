import ControlStack.Scenarios.SC16Deploy

namespace ControlStack.SC16

def Back_sc16_safe : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (ops : List Op),
    Good R h (run R h full init ops)

end ControlStack.SC16
