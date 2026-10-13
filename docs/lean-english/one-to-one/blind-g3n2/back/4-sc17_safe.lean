import ControlStack.Scenarios.SC17Infra

namespace ControlStack.SC17

-- Good constrains recorded applies and their ids, not intervening live states.
def Back_sc17_safe : Prop :=
  ∀ (E : Env) (g0 : List G) (ops : List Op),
    Good E (run E full (init g0) ops)

end ControlStack.SC17
