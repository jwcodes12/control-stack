namespace PL_g0_09
open ControlStack ControlStack.Deployment
def Back (R : SC26.Roles) (cap : Nat) (ops : List {o : SC26.Op // SC26.legal R o}) : Prop := (SC26.spec R cap).Inv ((SC26.sys R cap).run SC26.init ops) ∧ (SC26.sys R cap).effects SC26.init <+: (SC26.sys R cap).effects ((SC26.sys R cap).run SC26.init ops) ∧ ∀ e ∈ (SC26.sys R cap).effects ((SC26.sys R cap).run SC26.init ops), (SC26.spec R cap).ok ((SC26.sys R cap).run SC26.init ops) e
def Orig (R : SC26.Roles) (cap : Nat) (ops : List {o : SC26.Op // SC26.legal R o}) : Prop := (SC26.spec R cap).Inv ((SC26.sys R cap).run SC26.init ops) ∧ (SC26.sys R cap).effects SC26.init <+: (SC26.sys R cap).effects ((SC26.sys R cap).run SC26.init ops) ∧ ∀ e ∈ (SC26.sys R cap).effects ((SC26.sys R cap).run SC26.init ops), (SC26.spec R cap).ok ((SC26.sys R cap).run SC26.init ops) e
def Claim : Prop := ∀ (R : SC26.Roles) (cap : Nat) (ops : List {o : SC26.Op // SC26.legal R o}), (Back R cap ops ↔ Orig R cap ops)
def Witness : Prop := Accepted clean
end PL_g0_09
