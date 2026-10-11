namespace PL_g0_06
open ControlStack ControlStack.Deployment
def Back (d : IR) (r a : Node) (approvers admins : List Nat) (k : Nat) (tx : SC26.Tx) : Prop := a.uid ≠ r.uid
def Orig (d : IR) (r a : Node) (approvers admins : List Nat) (k : Nat) (tx : SC26.Tx) : Prop := SC26.legal (roles d r.uid approvers admins) (.bankCall a.uid k tx)
def Claim : Prop := ∀ (d : IR) (r a : Node) (approvers admins : List Nat) (k : Nat) (tx : SC26.Tx), (Back d r a approvers admins k tx ↔ Orig d r a approvers admins k tx)
def Witness : Prop := Accepted clean
end PL_g0_06
