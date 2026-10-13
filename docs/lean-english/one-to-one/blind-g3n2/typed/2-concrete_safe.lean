import ControlStack.Scenarios.SC16Refinement

namespace ControlStack.SC16Refinement

-- Deploy by the approved digest; the conclusion is the abstract Good predicate.
def Back_concrete_safe : Prop :=
  ∀ (R : SC16.Roles) (h : ℕ → ℕ) (ops : List COp),
    SC16.Good R h (α (runC R h false cinit ops))

end ControlStack.SC16Refinement
