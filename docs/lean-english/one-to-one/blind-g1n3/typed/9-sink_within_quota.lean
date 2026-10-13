import ControlStack.Scenarios.SC07Refinement

namespace ControlStack.SC07Refinement

def Back_sink_within_quota : Prop :=
  ∀ (K : CCfg) (ops : List COp) (w sink tolerance : ℕ),
    K.quotaRule = true →
    sink ≤ payloadIn (runC K cinit ops).fwd w →
    sink ≤ K.Q - 1 ∧ sink ≤ K.Q + tolerance

end ControlStack.SC07Refinement
