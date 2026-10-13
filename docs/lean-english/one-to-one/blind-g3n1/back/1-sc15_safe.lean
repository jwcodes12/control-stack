import ControlStack.Scenarios.SC15Review

namespace ControlStack.SC15

def Back_sc15_safe : Prop :=
  ∀ (E : Env) (ops : List Op),
    let s := run E full init ops
    ∀ c ∈ s.merged, MergeOk E s c

end ControlStack.SC15
