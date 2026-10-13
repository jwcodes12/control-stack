import ControlStack.EgressGate

namespace ControlStack.EgressGate

def Back_trace_safe : Prop :=
  ∀ (p : Policy) (s : State) (actions : List Action),
    Invariant p s → Invariant p (run p s actions)

end ControlStack.EgressGate
