namespace PL_bg0n1_4
open ControlStack ControlStack.Deployment

def Back : Prop :=
  ∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op),
    (SC26.run R cap SC26.full SC26.init ops).reserved.Nodup

def Orig : Prop :=
  ∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op),
    (SC26.run R cap SC26.full SC26.init ops).reserved.Nodup

def BackConclusion (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) : Prop :=
  (SC26.run R cap SC26.full SC26.init ops).reserved.Nodup

def OrigConclusion (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) : Prop :=
  (SC26.run R cap SC26.full SC26.init ops).reserved.Nodup

def Claim : Prop :=
  (Back ↔ (∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op),
    BackConclusion R cap ops)) ∧
  (Orig ↔ (∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op),
    OrigConclusion R cap ops)) ∧
  (∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op),
    (BackConclusion R cap ops ↔ OrigConclusion R cap ops))

def Witness : Prop :=
  (SC26.run twoRoles 1 SC26.full SC26.init ControlStack.Deployment.Witnesses.modelOps).reserved = [0] ∧ (SC26.run twoRoles 1 SC26.full SC26.init ControlStack.Deployment.Witnesses.modelOps).spent = 1

end PL_bg0n1_4
