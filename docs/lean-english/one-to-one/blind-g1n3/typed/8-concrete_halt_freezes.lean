import ControlStack.Scenarios.SC07Refinement

namespace ControlStack.SC07Refinement

def Back_concrete_halt_freezes : Prop :=
  ∀ (K : CCfg) («prefix» continuation : List COp),
    K.quotaRule = true →
    (runC K cinit «prefix»).halted = true →
    (runC K cinit («prefix» ++ continuation)).fwd =
      (runC K cinit «prefix»).fwd

end ControlStack.SC07Refinement
