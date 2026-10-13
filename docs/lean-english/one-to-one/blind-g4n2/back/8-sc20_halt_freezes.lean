namespace ControlStack.SC20

def Back_sc20_halt_freezes : Prop :=
  ∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true →
    run E full s ops = s

end ControlStack.SC20
