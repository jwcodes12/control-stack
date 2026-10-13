import ControlStack.Deployment.Contracts

namespace ControlStack.Deployment
open ControlStack

def Back_agent_call_legal : Prop :=
  ∀ (d : IR) (r a : Node) (approvers admins : List Nat)
      (key : Nat) (tx : SC26.Tx),
    Accepted d → r ∈ d.nodes → r.id = d.receiver →
    a ∈ d.nodes → a.agent = true →
    SC26.legal (roles d r.uid approvers admins)
      (SC26.Op.bankCall a.uid key tx)

end ControlStack.Deployment
