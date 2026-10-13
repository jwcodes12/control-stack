import ControlStack.Deployment.Contracts
import ControlStack.TrustedBroker

namespace ControlStack.Deployment
open ControlStack

def Back_broker_contract : Prop :=
  ∀ (R : TrustedBroker.Roles) (cap : Nat) (t : TrustedBroker.State),
    TrustedBroker.Trace R (TrustedBroker.initial cap) t →
    TrustedBroker.Safe t

end ControlStack.Deployment
