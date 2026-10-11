namespace PL_g0_08
open ControlStack ControlStack.Deployment
def Back (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) : Prop := (SC26.run R cap SC26.full SC26.init ops).reserved.Nodup
def Orig (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) : Prop := (SC26.run R cap SC26.full SC26.init ops).reserved.Nodup
def Claim : Prop := ∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op), (Back R cap ops ↔ Orig R cap ops)
def Witness : Prop := Accepted clean
end PL_g0_08
