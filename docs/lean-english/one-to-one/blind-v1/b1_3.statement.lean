namespace PL_b1_3
open ControlStack.Deployment

-- NOTE: Uses the real ControlStack.Deployment.Accepted predicate.
def Back_database_custody : Prop :=
  ∀ (d : IR) (e : Edge),
    ControlStack.Deployment.Accepted d →
    e ∈ d.edges → e.authority = true → e.target = d.database →
    e.source = d.receiver ∨ e.source = d.broker



def OrigConclusion (d : IR) (e : Edge) : Prop := e.source = d.receiver ∨ e.source = d.broker

def BackConclusion (d : IR) (e : Edge) : Prop := e.source = d.receiver ∨ e.source = d.broker

-- Shape records the blind quantifiers and hypotheses before comparing conclusions.
def Shape : Prop := Back_database_custody ↔ ∀ (d : IR) (e : Edge), Accepted d → e ∈ d.edges → e.authority = true → e.target = d.database →BackConclusion d e

def Claim : Prop := Shape ∧ ∀ (d : IR) (e : Edge), Accepted d → e ∈ d.edges → e.authority = true → e.target = d.database →(BackConclusion d e ↔ OrigConclusion d e)

def Witness : Prop := Accepted clean ∧ (⟨2,5,true,false,true⟩ : Edge) ∈ clean.edges ∧ (⟨2,5,true,false,true⟩ : Edge).authority = true ∧ (⟨2,5,true,false,true⟩ : Edge).target = clean.database
end PL_b1_3
