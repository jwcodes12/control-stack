namespace PL_g0_03
open ControlStack.Deployment
def Back : Prop := ∀ (d : IR) (e : Edge), Accepted d → e ∈ d.edges → e.authority = true → e.target = d.database → e.source = d.receiver
 def Claim : Prop := ¬ Back
 def Witness : Prop := Accepted clean
end PL_g0_03
