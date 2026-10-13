namespace PL_b1_2
open ControlStack.Deployment

-- NOTE: Uses the real ControlStack.Deployment.Accepted predicate.
def Back_exclusive_sink : Prop :=
  ∀ (d : IR) (e : Edge),
    ControlStack.Deployment.Accepted d →
    e ∈ d.edges → e.authority = true → e.target = d.sink →
    e.source = d.receiver



def OrigConclusion (d : IR) (e : Edge) : Prop := e.source = d.receiver

def BackConclusion (d : IR) (e : Edge) : Prop := e.source = d.receiver

-- Shape records the blind quantifiers and hypotheses before comparing conclusions.
def Shape : Prop := Back_exclusive_sink ↔ ∀ (d : IR) (e : Edge), Accepted d → e ∈ d.edges → e.authority = true → e.target = d.sink →BackConclusion d e

def Claim : Prop := Shape ∧ ∀ (d : IR) (e : Edge), Accepted d → e ∈ d.edges → e.authority = true → e.target = d.sink →(BackConclusion d e ↔ OrigConclusion d e)

def Witness : Prop := Accepted clean ∧ (⟨3,4,true,false,true⟩ : Edge) ∈ clean.edges ∧ (⟨3,4,true,false,true⟩ : Edge).authority = true ∧ (⟨3,4,true,false,true⟩ : Edge).target = clean.sink
end PL_b1_2
