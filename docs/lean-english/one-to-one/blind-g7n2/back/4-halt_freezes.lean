import ControlStack.Scenarios.SC28Budget

namespace ControlStack.SC28

def Back_halt_freezes : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op),
    s.halted = true →
    (run admins G full s ops).usage = s.usage

end ControlStack.SC28
