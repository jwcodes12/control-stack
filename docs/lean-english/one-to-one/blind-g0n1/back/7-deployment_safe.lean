import ControlStack.Deployment.Contracts

namespace ControlStack.Deployment
open ControlStack

def Back_deployment_safe : Prop :=
  ∀ (d : IR) (r : Node) (actualEdges : List Edge)
      (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op)
      (sinkEffects : List (Nat × SC26.Tx)),
    Accepted d → ExtractionFaithful d r actualEdges →
    ProtocolRefinement d r R cap ops sinkEffects →
    let s := SC26.run R cap SC26.full SC26.init ops
    (∀ e ∈ actualEdges, e.authority = true → e.target = d.sink →
      e.source = d.receiver) ∧
    (∀ e ∈ sinkEffects, ∃ req,
      SC26.reqOf s e.1 = some req ∧ req.tx = e.2 ∧
        e.1 ∈ s.reserved ∧ SC26.Approved R s e.1 req) ∧
    (sinkEffects.map Prod.fst).Nodup ∧
    (sinkEffects.map (fun e => e.2.amount)).sum ≤ cap ∧
    sinkEffects.length ≤ cap

end ControlStack.Deployment
