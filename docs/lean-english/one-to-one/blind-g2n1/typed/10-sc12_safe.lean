import ControlStack.Scenarios.SC12Persistence

namespace ControlStack.SC12

def Back_sc12_safe : Prop :=
  ∀ (admins : List ℕ) (ops : List Op),
    Good (run admins full init ops)

end ControlStack.SC12
