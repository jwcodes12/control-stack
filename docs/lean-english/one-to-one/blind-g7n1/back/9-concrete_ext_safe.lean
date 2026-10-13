namespace ControlStack.SC27Refinement

open ControlStack.SC27Chain (chainHead)
open ControlStack.SC27ExtensionOnly (Env)

-- NOTE
-- AMBIGUOUS: The English does not explicitly specify the starting state.
-- This reading uses the empty concrete state cinit. A reading allowing arbitrary
-- starting states would need hypotheses on their witness memory and anchor log.
def Back_concrete_ext_safe : Prop :=
  ∀ (E : Env) (ops : List COp),
    TraceInj E cinit ops →
    let final := runC E false cinit ops
    Set.InjOn (chainHead E.H E.h0)
      {l | l ∈ final.accepted ∨ ∃ a ∈ ancs final.wlog, a.2 = l} →
    ∀ m ∈ final.accepted,
      (∃ a ∈ ancs final.wlog, a.2 = m) ∧
      (∃ latest, final.ghostLast = some latest ∧ m <+: latest)

end ControlStack.SC27Refinement
