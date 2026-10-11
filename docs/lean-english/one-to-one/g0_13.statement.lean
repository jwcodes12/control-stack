namespace PL_g0_13
open ControlStack ControlStack.Deployment
def Back (d : IR) (a : Node) : Prop := ¬ AvoidedPath d a.id d.sink ∧ ¬ AvoidedPath d a.id d.database
def Orig (d : IR) (a : Node) : Prop := ¬ AvoidedPath d a.id d.sink ∧ ¬ AvoidedPath d a.id d.database
def Claim : Prop := ∀ (d : IR) (a : Node), (Back d a ↔ Orig d a)
def Witness : Prop := Accepted clean
end PL_g0_13
