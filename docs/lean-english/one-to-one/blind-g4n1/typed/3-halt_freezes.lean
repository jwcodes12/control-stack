import ControlStack.Scenarios.SC18Logging

namespace ControlStack.SC18

-- NOTE:
-- The conclusion concerns only released-list equality. The English aside
-- about the clock continuing to change while halted conflicts with step:
-- under full, a tick in a halted state leaves the state unchanged.
def Back_halt_freezes : Prop :=
  ∀ (admins : List ℕ) (trusted T : ℕ) (s : St) (ops : List Op),
    s.halted = true →
    (run admins trusted T full s ops).released = s.released

end ControlStack.SC18
