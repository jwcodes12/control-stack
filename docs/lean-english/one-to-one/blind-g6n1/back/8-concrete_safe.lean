import ControlStack.Scenarios.SC25Refinement

namespace ControlStack.SC25Refinement

open ControlStack.SC25

def Back_concrete_safe : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp),
    Good R h cls (α (runC R h cls false cinit ops))

end ControlStack.SC25Refinement
