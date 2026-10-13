import ControlStack.Deployment.Contracts

namespace ControlStack.Deployment
open ControlStack

def Back_one_use : Prop :=
  ∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op),
    (SC26.run R cap SC26.full SC26.init ops).reserved.Nodup

end ControlStack.Deployment
