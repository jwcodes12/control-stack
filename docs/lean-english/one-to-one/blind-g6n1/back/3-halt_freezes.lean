import ControlStack.Scenarios.SC25Audit

namespace ControlStack.SC25

def Back_halt_freezes : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St)
    (ops : List Op),
    s.halted = true →
    (run R h cls full s ops).executed = s.executed

end ControlStack.SC25
