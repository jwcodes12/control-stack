import ControlStack.Scenarios.SC19Prod

namespace ControlStack.SC19

-- Good uses DestroyOk: actual count, matching target/version snapshot,
-- a recorded verified index, an independent listed approver, and unique ids.
-- In this run, only a verifier-listed caller can add a verified index.
def Back_sc19_safe : Prop :=
  ∀ (E : Env) (ops : List Op),
    Good E (run E full init ops)

end ControlStack.SC19
