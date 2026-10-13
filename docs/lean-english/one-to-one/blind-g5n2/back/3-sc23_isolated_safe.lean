import ControlStack.Scenarios.SC23Isolation

namespace ControlStack.SC23Isolation

-- ActOk requires a matching recorded nonce, tool, exact values, and user caller.
-- It imposes neither confirmation uniqueness across actions nor a condition
-- on untainted actions or non-sensitive tools.
def Back_sc23_isolated_safe : Prop :=
  ∀ (E : Env) (ops : List Op),
    let s := run E full init ops
    ∀ x ∈ s.executed, ActOk E s x

end ControlStack.SC23Isolation
