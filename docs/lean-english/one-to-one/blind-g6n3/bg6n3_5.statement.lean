namespace PL_bg6n3_5
open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26Liveness ControlStack.SC26Liveness.Concrete ControlStack.SC26LossyLiveness ControlStack.SC26LossyHalt

def Back_lossy_halt_keys : Prop :=
  ∀ (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp),
    s.halted = true →
    (∀ o ∈ ops, legalL R o) →
    ∀ k ∈ (runLH R cap true s ops).bank.map Prod.fst,
      k ∈ s.bank.map Prod.fst ∨ k ∈ s.wire.map Prod.fst


def BackAt (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (k : ℕ) : Prop :=
  k ∈ (runLH R cap true s ops).bank.map Prod.fst →
    k ∈ s.bank.map Prod.fst ∨ k ∈ s.wire.map Prod.fst

def OrigAt (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (k : ℕ) : Prop :=
  k ∈ (runL R cap true s ops).bank.map Prod.fst →
    k ∈ s.bank.map Prod.fst ∨ k ∈ s.wire.map Prod.fst

def Pointwise : Prop :=
  ∀ (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (k : ℕ),
    s.halted = true → (∀ o ∈ ops, legalL R o) →
    (BackAt R cap s ops k ↔ OrigAt R cap s ops k)

def start : CSt := { strandedState with wire := [(0, wTx)] }
def trace : List LOp := [.dup 0, .drop 0, .base .crash, .base .recover, .deliverAt 0]
def Witness : Prop :=
  start.halted = true ∧ start.bank = [] ∧ 0 ∈ start.wire.map Prod.fst ∧
  (∀ o ∈ trace, legalL R0 o) ∧
  (runLH R0 10 true start trace).bank = [(0, wTx)]

def OriginalSignature : Prop :=
  ∀ (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o)
    (hh : s.halted = true) (x : ℕ) (hx : x ∈ (runL R cap true s ops).bank.map Prod.fst),
    x ∈ s.bank.map Prod.fst ∨ x ∈ s.wire.map Prod.fst

def BackShape : Prop := Back_lossy_halt_keys ↔

  ∀ (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp),
    s.halted = true →
    (∀ o ∈ ops, legalL R o) →
    ∀ k, BackAt R cap s ops k

def OriginalShape : Prop := OriginalSignature ↔
  ∀ (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (hops : ∀ o ∈ ops, legalL R o)
    (hh : s.halted = true) (x : ℕ), OrigAt R cap s ops x

def Claim : Prop := Pointwise ∧ BackShape ∧ OriginalShape

end PL_bg6n3_5
