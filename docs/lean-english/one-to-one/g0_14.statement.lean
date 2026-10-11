namespace PL_g0_14
open ControlStack ControlStack.Deployment
def Back (larger : IR) (start target : Nat) : Prop := AvoidedPath larger start target
def Orig (larger : IR) (start target : Nat) : Prop := AvoidedPath larger start target
def Claim : Prop := ∀ (larger : IR) (start target : Nat), (Back larger start target ↔ Orig larger start target)
def Witness : Prop := Accepted clean
end PL_g0_14
