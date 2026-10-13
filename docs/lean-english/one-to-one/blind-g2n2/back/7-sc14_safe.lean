import ControlStack.Scenarios.SC14Runaway

namespace ControlStack.SC14

def Back_sc14_safe : Prop :=
  ∀ (E : Env) (exp : ℕ) (ops : List Op),
    (∀ o ∈ ops, legal o) → Good E (run E full (init exp) ops)

end ControlStack.SC14
