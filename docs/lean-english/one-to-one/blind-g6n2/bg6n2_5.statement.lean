namespace PL_bg6n2_5
open ControlStack.SC26
open ControlStack.SC26Refinement

open ControlStack.SC26

def Back : Prop :=
  ∀ (R : Roles) (cap : ℕ) (ops : List COp),
    (∀ o ∈ ops, legalC R o) →
    Good R cap (α (runC R cap true cinit ops))


def BackAt (R : Roles) (cap : ℕ) (s : CSt) : Prop := Good R cap (α s)
def OrigAt (R : Roles) (cap : ℕ) (s : CSt) : Prop := Good R cap (α s)
def BackEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (ops : List COp), (∀ o ∈ ops, legalC R o) →
    BackAt R cap (runC R cap true cinit ops)
def OrigEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (ops : List COp), (∀ o ∈ ops, legalC R o) →
    OrigAt R cap (runC R cap true cinit ops)
def Claim : Prop := (Back ↔ BackEnvelope) ∧ (∀ (R : Roles) (cap : ℕ) (s : CSt), BackAt R cap s ↔ OrigAt R cap s)
def honestCOps : List COp := [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .deliver 0, .transmit 0, .bankProcess 0]
def Witness : Prop := (∀ o ∈ honestCOps, legalC R0 o) ∧
  (runC R0 20 true cinit honestCOps).bank = [(0, tx1)]
end PL_bg6n2_5
