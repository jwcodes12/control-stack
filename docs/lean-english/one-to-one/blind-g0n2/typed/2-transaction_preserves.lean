import ControlStack.TrustedBroker

namespace ControlStack.TrustedBroker

def Back_transaction_preserves : Prop :=
  ∀ (roles : Roles) (s t : State),
    Safe s → Step roles s t → Safe t

end ControlStack.TrustedBroker
