import ControlStack.Scenarios.SC27Refinement

namespace ControlStack.SC27Refinement

open ControlStack.SC27ExtensionOnly (Env)

-- NOTE
-- AMBIGUOUS: The English specifies the trace split but not its starting state.
-- This reading starts the combined trace at cinit. Arbitrary starting states
-- would require additional hypotheses on their witness memory and anchor log.
def Back_concrete_tampered_never_anchored : Prop :=
  ∀ (E : Env) (first second : List COp) (l : List ℕ),
    TraceInj E cinit (first ++ second) →
    let middle := runC E false cinit first
    let final := runC E false cinit (first ++ second)
    (∃ a ∈ ancs middle.wlog, a.2 = l) →
    ∀ a ∈ ancs final.wlog,
      a ∈ ancs middle.wlog ∨ l <+: a.2

end ControlStack.SC27Refinement
