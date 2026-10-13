namespace PL_b1_12
open ControlStack.Deployment

-- NOTE: Uses the real ControlStack.Deployment.Accepted predicate.
-- AvoidedPath is the supplied relation, including its zero-step path.
def Back_accepted_no_avoided_path : Prop :=
  ∀ (d : IR) (a : Node),
    ControlStack.Deployment.Accepted d →
    a ∈ d.nodes → a.agent = true →
    (¬ ControlStack.Deployment.AvoidedPath d a.id d.sink) ∧
    (¬ ControlStack.Deployment.AvoidedPath d a.id d.database)



def OrigConclusion (d : IR) (a : Node) : Prop := ¬ AvoidedPath d a.id d.sink ∧ ¬ AvoidedPath d a.id d.database

def BackConclusion (d : IR) (a : Node) : Prop := ¬ AvoidedPath d a.id d.sink ∧ ¬ AvoidedPath d a.id d.database

-- Shape records the blind quantifiers and hypotheses before comparing conclusions.
def Shape : Prop := Back_accepted_no_avoided_path ↔ ∀ (d : IR) (a : Node), Accepted d → a ∈ d.nodes → a.agent = true →BackConclusion d a

def Claim : Prop := Shape ∧ ∀ (d : IR) (a : Node), Accepted d → a ∈ d.nodes → a.agent = true →(BackConclusion d a ↔ OrigConclusion d a)

def Witness : Prop := Accepted clean ∧ Witnesses.agentA ∈ clean.nodes ∧ Witnesses.agentA.agent = true
end PL_b1_12
