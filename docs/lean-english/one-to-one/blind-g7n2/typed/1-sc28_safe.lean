import ControlStack.Scenarios.SC28Budget

namespace ControlStack.SC28

def Back_sc28_safe : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (ops : List Op),
    (∀ o ∈ ops, legal o) →
    Good G (run admins G full init ops)

end ControlStack.SC28
