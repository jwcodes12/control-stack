import ControlStack.Scenarios.SC08Exec

namespace ControlStack.SC08

def Back_sc08_safe : Prop :=
  ∀ (E : Env) (files : List (ℕ × ℕ)) (ops : List Op),
    Good E (run E full (⟨files, [], false⟩ : St) ops)

end ControlStack.SC08
