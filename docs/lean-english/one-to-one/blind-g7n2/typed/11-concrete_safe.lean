import ControlStack.Scenarios.SC28Refinement

namespace ControlStack.SC28Refinement

def Back_concrete_safe : Prop :=
  ∀ (G : ℕ) (ops : List COp),
    let s := runC G cinit ops
    runCounter s ≤ G ∧
      (∀ lid, counter s lid ≤ (limitOf s lid).getD 0) ∧
      s.acct.length ≤ G

end ControlStack.SC28Refinement
