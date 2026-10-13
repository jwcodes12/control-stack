import ControlStack.TrustedBroker

namespace ControlStack.TrustedBroker

def Back_transaction_coherent : Prop :=
  ∀ (roles : Roles) (s t : State),
    Coherent s → Step roles s t → Coherent t

end ControlStack.TrustedBroker
