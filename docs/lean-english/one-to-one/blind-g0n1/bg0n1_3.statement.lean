namespace PL_bg0n1_3
open ControlStack ControlStack.Deployment

def Back : Prop :=
  ∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op),
    (∀ o ∈ ops, SC26.legal R o) →
    SC26.Good R cap (SC26.run R cap SC26.full SC26.init ops)

def Orig : Prop :=
  ∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op)
    (hops : ∀ o ∈ ops, SC26.legal R o),
    SC26.Good R cap (SC26.run R cap SC26.full SC26.init ops)

def BackConclusion (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) : Prop :=
  SC26.Good R cap (SC26.run R cap SC26.full SC26.init ops)

def OrigConclusion (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) : Prop :=
  SC26.Good R cap (SC26.run R cap SC26.full SC26.init ops)

def Claim : Prop :=
  (Back ↔ (∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op),
    (∀ o ∈ ops, SC26.legal R o) →
    BackConclusion R cap ops)) ∧
  (Orig ↔ (∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op)
    (hops : ∀ o ∈ ops, SC26.legal R o),
    OrigConclusion R cap ops)) ∧
  (∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op), (∀ o ∈ ops, SC26.legal R o) →
    (BackConclusion R cap ops ↔ OrigConclusion R cap ops))

def Witness : Prop :=
  (∀ o ∈ ControlStack.Deployment.Witnesses.modelOps, SC26.legal twoRoles o) ∧ (SC26.run twoRoles 1 SC26.full SC26.init ControlStack.Deployment.Witnesses.modelOps).bank = [(0,payload)]

end PL_bg0n1_3
