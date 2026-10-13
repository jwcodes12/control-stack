import ControlStack.Scenarios.EvalIntegrity

namespace ControlStack.EvalIntegrity

-- The claim concerns published snapshots only, including truth only for
-- tasks recorded as re-executed in that particular snapshot.
def Back_sc21_safe : Prop :=
  ∀ (E : Env) (ops : List Op),
    ∀ p ∈ (run E full init ops).published, PubOk E p

end ControlStack.EvalIntegrity
