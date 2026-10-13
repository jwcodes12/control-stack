import ControlStack.Scenarios.SC25Audit

namespace ControlStack.SC25

def Back_sc25_safe : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op),
    Good R h cls (run R h cls full init ops)

end ControlStack.SC25
