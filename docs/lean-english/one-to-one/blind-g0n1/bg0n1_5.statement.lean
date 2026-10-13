namespace PL_bg0n1_5
open ControlStack ControlStack.Deployment

def Back : Prop :=
  ∀ (R : SC26.Roles) (cap : Nat)
      (ops : List {o : SC26.Op // SC26.legal R o}),
    let G := SC26.sys R cap
    let s := Gate.System.run G SC26.init ops
    (SC26.spec R cap).Inv s ∧
      (G.effects SC26.init <+: G.effects s) ∧
      (∀ e ∈ G.effects s, (SC26.spec R cap).ok s e)

def Orig : Prop :=
  ∀ (R : SC26.Roles) (cap : Nat)
    (ops : List {o : SC26.Op // SC26.legal R o}),
    (SC26.spec R cap).Inv ((SC26.sys R cap).run SC26.init ops) ∧
    (SC26.sys R cap).effects SC26.init <+: (SC26.sys R cap).effects ((SC26.sys R cap).run SC26.init ops) ∧
    ∀ e ∈ (SC26.sys R cap).effects ((SC26.sys R cap).run SC26.init ops),
      (SC26.spec R cap).ok ((SC26.sys R cap).run SC26.init ops) e

def BackConclusion (R : SC26.Roles) (cap : Nat) (ops : List {o : SC26.Op // SC26.legal R o}) : Prop :=
  let G := SC26.sys R cap
  let s := Gate.System.run G SC26.init ops
  (SC26.spec R cap).Inv s ∧
    (G.effects SC26.init <+: G.effects s) ∧
    (∀ e ∈ G.effects s, (SC26.spec R cap).ok s e)

def OrigConclusion (R : SC26.Roles) (cap : Nat) (ops : List {o : SC26.Op // SC26.legal R o}) : Prop :=
  (SC26.spec R cap).Inv ((SC26.sys R cap).run SC26.init ops) ∧
    (SC26.sys R cap).effects SC26.init <+: (SC26.sys R cap).effects ((SC26.sys R cap).run SC26.init ops) ∧
    ∀ e ∈ (SC26.sys R cap).effects ((SC26.sys R cap).run SC26.init ops),
      (SC26.spec R cap).ok ((SC26.sys R cap).run SC26.init ops) e

def Claim : Prop :=
  (Back ↔ (∀ (R : SC26.Roles) (cap : Nat)
      (ops : List {o : SC26.Op // SC26.legal R o}),
    BackConclusion R cap ops)) ∧
  (Orig ↔ (∀ (R : SC26.Roles) (cap : Nat)
    (ops : List {o : SC26.Op // SC26.legal R o}),
    OrigConclusion R cap ops)) ∧
  (∀ (R : SC26.Roles) (cap : Nat) (ops : List {o : SC26.Op // SC26.legal R o}),
    (BackConclusion R cap ops ↔ OrigConclusion R cap ops))

def Witness : Prop :=
  ∃ ops : List {o : SC26.Op // SC26.legal twoRoles o}, ops.length = 5 ∧ (SC26.sys twoRoles 1).effects ((SC26.sys twoRoles 1).run SC26.init ops) = [(0,payload)]

end PL_bg0n1_5
