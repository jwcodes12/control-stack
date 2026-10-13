import ControlStack.Scenarios.SC26Refinement

namespace ControlStack.SC26Refinement

open ControlStack.SC26

def Back_concrete_halt : Prop :=
  ∀ (R : Roles) (cap : ℕ) (s : CSt) (ops : List COp),
    s.halted = true →
    (∀ o ∈ ops, legalC R o) →
    let t := runC R cap true s ops
    t.wire = s.wire ∧
    (∀ e ∈ t.bank, e ∈ s.bank ∨ e ∈ s.wire)

end ControlStack.SC26Refinement
