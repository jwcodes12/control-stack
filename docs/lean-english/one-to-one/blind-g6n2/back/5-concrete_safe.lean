namespace ControlStack.SC26Refinement

open ControlStack.SC26

def Back_concrete_safe : Prop :=
  ∀ (R : Roles) (cap : ℕ) (ops : List COp),
    (∀ o ∈ ops, legalC R o) →
    Good R cap (α (runC R cap true cinit ops))

end ControlStack.SC26Refinement
