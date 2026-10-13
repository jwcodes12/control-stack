namespace ControlStack.SC27Chain

def Back_sc27_safe : Prop :=
  ∀ (E : Env) (ops : List Op),
    let final := run E full init ops
    Set.InjOn (chainHead E.H E.h0)
      {l | l ∈ final.accepted ∨ ∃ a ∈ final.anchors, a.2 = some l} →
    ∀ m ∈ final.accepted, ∃ a ∈ final.anchors, a.2 = some m

end ControlStack.SC27Chain
