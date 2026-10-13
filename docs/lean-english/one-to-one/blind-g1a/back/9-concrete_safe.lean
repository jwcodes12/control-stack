import ControlStack.Scenarios.SC07Refinement

namespace ControlStack.SC07Refinement

def Back_concrete_safe : Prop :=
  ∀ (K : CCfg) (ops : List COp),
    K.quotaRule = true →
    let s := runC K cinit ops
    (∀ r ∈ s.fwd, (r.ip, r.port) ∈ K.allow) ∧
      (∀ w : ℕ, payloadIn s.fwd w ≤ K.Q - 1)

end ControlStack.SC07Refinement
