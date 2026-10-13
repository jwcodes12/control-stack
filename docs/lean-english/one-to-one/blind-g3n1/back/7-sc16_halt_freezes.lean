import ControlStack.Scenarios.SC16Deploy

namespace ControlStack.SC16

def Back_halt_freezes : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (s : St) (ops : List Op),
    s.halted = true → run R h full s ops = s

end ControlStack.SC16
