namespace PL_g0_05
open ControlStack.Deployment
def Back : Prop := ∀ (d : IR) (r : Node), Accepted d → r ∈ d.nodes → r.id = d.receiver → ∀ a ∈ d.nodes, a.uid ≠ r.uid
 def Claim : Prop := ¬ Back
 def Witness : Prop := Accepted clean
end PL_g0_05
