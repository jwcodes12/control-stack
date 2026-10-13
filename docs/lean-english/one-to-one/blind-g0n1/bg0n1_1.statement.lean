namespace PL_bg0n1_1
open ControlStack ControlStack.Deployment

def Back : Prop :=
  ∀ (d : IR) (actual : List Edge),
    Accepted d → Faithful d actual →
    ∀ e ∈ actual, e.authority = true → e.target = d.sink →
      e.source = d.receiver

def Orig : Prop :=
  ∀ (d : IR) (actual : List Edge) (h : Accepted d)
    (faithful : Faithful d actual) (e : Edge) (member : e ∈ actual)
    (authority : e.authority = true) (sink : e.target = d.sink),
    e.source = d.receiver

def BackConclusion (d : IR) (e : Edge) : Prop :=
  e.source = d.receiver

def OrigConclusion (d : IR) (e : Edge) : Prop :=
  e.source = d.receiver

def Claim : Prop :=
  (Back ↔ (∀ (d : IR) (actual : List Edge),
    Accepted d → Faithful d actual →
    ∀ e ∈ actual, e.authority = true → e.target = d.sink →
      BackConclusion d e)) ∧
  (Orig ↔ (∀ (d : IR) (actual : List Edge) (h : Accepted d)
    (faithful : Faithful d actual) (e : Edge) (member : e ∈ actual)
    (authority : e.authority = true) (sink : e.target = d.sink),
    OrigConclusion d e)) ∧
  (∀ (d : IR) (actual : List Edge) (e : Edge), Accepted d → Faithful d actual → e ∈ actual → e.authority = true → e.target = d.sink →
    (BackConclusion d e ↔ OrigConclusion d e))

def Witness : Prop :=
  Accepted clean ∧ Faithful clean clean.edges ∧ (ControlStack.Deployment.Witnesses.receiverNode ∈ clean.nodes) ∧ ∃ e ∈ clean.edges, e.authority = true ∧ e.target = clean.sink

end PL_bg0n1_1
