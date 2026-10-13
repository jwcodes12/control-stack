import ControlStack.TrustedBroker

namespace ControlStack.TrustedBroker

def Back_trace_preserves : Prop :=
  ∀ (roles : Roles) (s t : State),
    Safe s → Trace roles s t → Safe t

end ControlStack.TrustedBroker
