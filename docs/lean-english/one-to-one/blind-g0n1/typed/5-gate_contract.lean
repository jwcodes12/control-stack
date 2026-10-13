import ControlStack.Deployment.Contracts

namespace ControlStack.Deployment
open ControlStack

def Back_gate_contract : Prop :=
  ∀ (R : SC26.Roles) (cap : Nat)
      (ops : List {o : SC26.Op // SC26.legal R o}),
    let G := SC26.sys R cap
    let s := Gate.System.run G SC26.init ops
    (SC26.spec R cap).Inv s ∧
      (G.effects SC26.init <+: G.effects s) ∧
      (∀ e ∈ G.effects s, (SC26.spec R cap).ok s e)

end ControlStack.Deployment
