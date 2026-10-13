namespace PL_bg0n1_10
open ControlStack ControlStack.Deployment

def Back : Prop :=
  sinkOnly.nodes = clean.nodes ∧
  (∀ e ∈ sinkOnly.edges, e ∈ clean.edges) ∧
  (∃ e ∈ sinkOnly.edges,
    e.source = sinkOnly.receiver ∧ e.target = sinkOnly.sink ∧ e.write = true) ∧
  Accepted clean ∧ ¬ Accepted sinkOnly

def Orig : Prop :=
  sinkOnly.nodes = clean.nodes ∧ (∀ e ∈ sinkOnly.edges, e ∈ clean.edges) ∧
    (∃ e ∈ sinkOnly.edges, e.source = sinkOnly.receiver ∧ e.target = sinkOnly.sink ∧ e.write = true) ∧
    Accepted clean ∧ ¬ Accepted sinkOnly

def BackConclusion (small large : IR) : Prop :=
  small.nodes = large.nodes ∧
  (∀ e ∈ small.edges, e ∈ large.edges) ∧
  (∃ e ∈ small.edges,
    e.source = small.receiver ∧ e.target = small.sink ∧ e.write = true) ∧
  Accepted large ∧ ¬ Accepted small

def OrigConclusion (small large : IR) : Prop :=
  small.nodes = large.nodes ∧ (∀ e ∈ small.edges, e ∈ large.edges) ∧
    (∃ e ∈ small.edges, e.source = small.receiver ∧ e.target = small.sink ∧ e.write = true) ∧
    Accepted large ∧ ¬ Accepted small

def Claim : Prop :=
  (Back ↔ (BackConclusion sinkOnly clean)) ∧
  (Orig ↔ (OrigConclusion sinkOnly clean)) ∧
  (∀ (small large : IR), BackConclusion small large ↔ OrigConclusion small large)

def Witness : Prop :=
  sinkOnly.edges ≠ clean.edges ∧ sinkOnly.nodes.length = 6 ∧ Accepted clean ∧ ¬ Accepted sinkOnly

end PL_bg0n1_10
