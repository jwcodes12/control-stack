namespace PL_bg6n3_3
open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26Liveness ControlStack.SC26Liveness.Concrete ControlStack.SC26LossyLiveness ControlStack.SC26LossyHalt

def Back_lossy_safe : Prop :=
  ∀ (R : Roles) (cap : ℕ) (ops : List LOp),
    (∀ o ∈ ops, legalL R o) →
    Good R cap (α (runL R cap true cinit ops))


def BackAt (R : Roles) (cap : ℕ) (ops : List LOp) : Prop :=
  Good R cap (α (runL R cap true cinit ops))
def OrigAt (R : Roles) (cap : ℕ) (ops : List LOp) : Prop :=
  Good R cap (α (runL R cap true cinit ops))
def Pointwise : Prop :=
  ∀ (R : Roles) (cap : ℕ) (ops : List LOp), (∀ o ∈ ops, legalL R o) →
    (BackAt R cap ops ↔ OrigAt R cap ops)
def trace : List LOp := setupOps ++ [.base .recover, .dup 0, .drop 0, .deliverAt 0]
def Witness : Prop :=
  (∀ o ∈ trace, legalL R0 o) ∧
  (runL R0 10 true cinit trace).bank = [(0, wTx)] ∧
  (runL R0 10 true cinit trace).spent = 10

def OriginalSignature : Prop :=
  ∀ (R : Roles) (cap : ℕ) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o),
    Good R cap (α (runL R cap true cinit ops))

def BackShape : Prop := Back_lossy_safe ↔

  ∀ (R : Roles) (cap : ℕ) (ops : List LOp),
    (∀ o ∈ ops, legalL R o) →
    BackAt R cap ops

def OriginalShape : Prop := OriginalSignature ↔
  ∀ (R : Roles) (cap : ℕ) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o), OrigAt R cap ops

def Claim : Prop := Pointwise ∧ BackShape ∧ OriginalShape

end PL_bg6n3_3
