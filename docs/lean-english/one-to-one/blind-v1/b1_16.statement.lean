namespace PL_b1_16
open ControlStack.Deployment

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



def OrigConclusion (d : IR) (r : Node) (actualEdges : List Edge) (R : ControlStack.TrustedBroker.Roles) (cap : Nat) (t : ControlStack.TrustedBroker.State) (sinkNonces : List Nat) : Prop := (∀ e ∈ actualEdges, e.authority = true → e.target = d.sink → e.source = d.receiver) ∧ ¬ R.agent r.uid ∧ sinkNonces.Nodup ∧ sinkNonces.length ≤ cap ∧ (∀ nonce ∈ sinkNonces, ∃ a : ControlStack.TrustedBroker.Approval, t.approvals nonce = some a ∧ a.used = true)

def BackConclusion (d : IR) (r : Node) (actualEdges : List Edge) (R : ControlStack.TrustedBroker.Roles) (cap : Nat) (t : ControlStack.TrustedBroker.State) (sinkNonces : List Nat) : Prop := (∀ e ∈ actualEdges, e.authority = true → e.target = d.sink → e.source = d.receiver) ∧ ¬ R.agent r.uid ∧ sinkNonces.Nodup ∧ sinkNonces.length ≤ cap ∧ (∀ nonce ∈ sinkNonces, ∃ a : ControlStack.TrustedBroker.Approval, t.approvals nonce = some a ∧ a.used = true)

-- Shape records the blind quantifiers and hypotheses before comparing conclusions.
def Shape : Prop := Back_deployment_broker_safe ↔ ∀ (d : IR) (r : Node) (actualEdges : List Edge) (R : ControlStack.TrustedBroker.Roles) (cap : Nat) (t : ControlStack.TrustedBroker.State) (sinkNonces : List Nat), Accepted d → ExtractionFaithful d r actualEdges → BrokerProtocolRefinement d R cap t sinkNonces →BackConclusion d r actualEdges R cap t sinkNonces

def Claim : Prop := Shape ∧ ∀ (d : IR) (r : Node) (actualEdges : List Edge) (R : ControlStack.TrustedBroker.Roles) (cap : Nat) (t : ControlStack.TrustedBroker.State) (sinkNonces : List Nat), Accepted d → ExtractionFaithful d r actualEdges → BrokerProtocolRefinement d R cap t sinkNonces →(BackConclusion d r actualEdges R cap t sinkNonces ↔ OrigConclusion d r actualEdges R cap t sinkNonces)

def Witness : Prop := Accepted clean ∧ ExtractionFaithful clean Witnesses.receiverNode clean.edges ∧ BrokerProtocolRefinement clean Witnesses.R 1 Witnesses.s5 [7]
end PL_b1_16
