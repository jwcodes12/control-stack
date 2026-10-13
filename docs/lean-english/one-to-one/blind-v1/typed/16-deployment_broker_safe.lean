import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace ControlStack.Deployment

-- NOTE: Uses the real ControlStack.Deployment.Accepted predicate.
-- Faithful extraction and the broker/publication refinement remain hypotheses.
def Back_deployment_broker_safe : Prop :=
  ∀ (d : IR) (r : Node) (actualEdges : List Edge)
    (R : ControlStack.TrustedBroker.Roles) (cap : Nat)
    (t : ControlStack.TrustedBroker.State) (sinkNonces : List Nat),
    ControlStack.Deployment.Accepted d →
    ControlStack.Deployment.ExtractionFaithful d r actualEdges →
    ControlStack.Deployment.BrokerProtocolRefinement d R cap t sinkNonces →
    (∀ e ∈ actualEdges, e.authority = true → e.target = d.sink →
      e.source = d.receiver) ∧
    (¬ R.agent r.uid) ∧
    sinkNonces.Nodup ∧
    sinkNonces.length ≤ cap ∧
    (∀ nonce ∈ sinkNonces,
      ∃ a : ControlStack.TrustedBroker.Approval,
        t.approvals nonce = some a ∧ a.used = true)

end ControlStack.Deployment
