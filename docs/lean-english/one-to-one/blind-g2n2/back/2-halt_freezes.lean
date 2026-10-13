import ControlStack.Scenarios.SC12Persistence

namespace ControlStack.SC12

def Back_halt_freezes : Prop :=
  ∀ (admins : List ℕ) (s : St) (ops : List Op),
    s.halted = true → run admins full s ops = s

end ControlStack.SC12
