import ControlStack.Deployment.Contracts

namespace ControlStack.Deployment
open ControlStack

def Back_protocol_safe : Prop :=
  ∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op),
    (∀ o ∈ ops, SC26.legal R o) →
    SC26.Good R cap (SC26.run R cap SC26.full SC26.init ops)

end ControlStack.Deployment
