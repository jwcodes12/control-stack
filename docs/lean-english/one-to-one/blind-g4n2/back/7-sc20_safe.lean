namespace ControlStack.SC20

-- Good admits only registered digests or digests in listed-reviewer promotions.
def Back_sc20_safe : Prop :=
  ∀ (E : Env) (ops : List Op),
    Good E (run E full init ops)

end ControlStack.SC20
