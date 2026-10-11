namespace PL_g0_15
open ControlStack ControlStack.Deployment
def Back  : Prop := sinkOnly.nodes = clean.nodes ∧ (∀ e ∈ sinkOnly.edges, e ∈ clean.edges) ∧ (∃ e ∈ sinkOnly.edges, e.source = sinkOnly.receiver ∧ e.target = sinkOnly.sink ∧ e.write = true) ∧ Accepted clean ∧ ¬ Accepted sinkOnly
def Orig  : Prop := sinkOnly.nodes = clean.nodes ∧ (∀ e ∈ sinkOnly.edges, e ∈ clean.edges) ∧ (∃ e ∈ sinkOnly.edges, e.source = sinkOnly.receiver ∧ e.target = sinkOnly.sink ∧ e.write = true) ∧ Accepted clean ∧ ¬ Accepted sinkOnly
def Claim : Prop := (Back  ↔ Orig )
def Witness : Prop := Accepted clean
end PL_g0_15
