namespace ControlStack.SC27ExtensionOnly

open ControlStack.SC27Chain (chainHead)

-- NOTE
-- AMBIGUOUS: The English does not explicitly specify the starting state.
-- This reading uses the empty state init. A reading allowing arbitrary starting
-- states would need initial-state hypotheses to obtain the stated safety.
def Back_sc27_ext_safe : Prop :=
  ∀ (E : Env) (ops : List Op),
    let final := run E true init ops
    Set.InjOn (chainHead E.H E.h0)
      {l | l ∈ final.accepted ∨ ∃ a ∈ final.anchors, a.2 = l} →
    ∀ m ∈ final.accepted,
      (∃ a ∈ final.anchors, a.2 = m) ∧
      (∃ latest, final.last = some latest ∧ m <+: latest)

end ControlStack.SC27ExtensionOnly
