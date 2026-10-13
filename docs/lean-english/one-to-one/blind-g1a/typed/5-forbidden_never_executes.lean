import ControlStack.Scenarios.SC05Signal

namespace ControlStack.SC05

def Back_forbidden_never_executes : Prop :=
  ∀ (forbidden : List ℕ) (ops : List Op),
    ∀ a ∈ ControlStack.Gate.System.run (sys forbidden) [] ops,
      a ∉ forbidden

end ControlStack.SC05
