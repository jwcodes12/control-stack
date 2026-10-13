import ControlStack.EgressGate

namespace ControlStack.EgressGate

def Back_step_safe : Prop :=
  ∀ (p : Policy) (s : State) (a : Action),
    Invariant p s → Invariant p (step p s a)

end ControlStack.EgressGate
