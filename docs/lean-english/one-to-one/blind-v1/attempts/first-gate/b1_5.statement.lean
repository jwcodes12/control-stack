namespace PL_b1_5
open ControlStack.Deployment

-- NOTE: Uses the real ControlStack.Deployment.Accepted predicate.
def Back_agent_not_receiver_uid : Prop :=
  ∀ (d : IR) (r a : Node),
    ControlStack.Deployment.Accepted d →
    r ∈ d.nodes → r.id = d.receiver →
    a ∈ d.nodes → a.agent = true →
    a.uid ≠ r.uid



def OrigConclusion (d : IR) (r a : Node) : Prop := a.uid ≠ r.uid

def BackConclusion (d : IR) (r a : Node) : Prop := a.uid ≠ r.uid

-- Shape records the blind quantifiers and hypotheses before comparing conclusions.
def Shape : Prop := Back_agent_not_receiver_uid ↔ ∀ (d : IR) (r a : Node), Accepted d → r ∈ d.nodes → r.id = d.receiver → a ∈ d.nodes → a.agent = true →BackConclusion d r a

def Claim : Prop := Shape ∧ ∀ (d : IR) (r a : Node), Accepted d → r ∈ d.nodes → r.id = d.receiver → a ∈ d.nodes → a.agent = true →(BackConclusion d r a ↔ OrigConclusion d r a)

def Witness : Prop := Accepted clean ∧ Witnesses.receiverNode ∈ clean.nodes ∧ Witnesses.receiverNode.id = clean.receiver ∧ Witnesses.agentA ∈ clean.nodes ∧ Witnesses.agentA.agent = true
end PL_b1_5
