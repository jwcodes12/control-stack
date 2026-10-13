import ControlStack.Scenarios.SC28Refinement

namespace ControlStack.SC28Refinement

def Back_exclusive_placement_safe : Prop :=
  ∀ (G : ℕ) (ops : List COp),
    (∀ o ∈ ops, isUnplaced o = false) →
    let s := runC G cinit ops
    s.outside = [] ∧ realTotal s ≤ G

end ControlStack.SC28Refinement
