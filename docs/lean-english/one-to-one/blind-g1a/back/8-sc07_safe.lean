import ControlStack.Scenarios.SC07Liveness

namespace ControlStack.SC07Liveness

def Back_sc07_safe : Prop :=
  ∀ (E : Env) (ops : List Op),
    let s := run E full init ops
    (∀ e ∈ s.log, e.dest ∈ E.allow) ∧
      (∀ w : ℕ, wsum s w ≤ E.q)

end ControlStack.SC07Liveness
