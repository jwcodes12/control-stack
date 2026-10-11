namespace PL_g0_12
open ControlStack.Deployment
def Back : Prop := ∀ (d : IR) (a : Node) (target : Nat), Accepted d → a ∈ d.nodes → a.agent = true → target ≠ a.id → ¬ AvoidedPath d a.id target
 def Claim : Prop := ¬ Back
 def Witness : Prop := Accepted clean
end PL_g0_12
