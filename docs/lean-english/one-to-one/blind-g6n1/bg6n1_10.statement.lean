namespace PL_bg6n1_10

open ControlStack.SC26

def FrozenBack : Prop :=
  ∀ (R : Roles) (cap : ℕ) (ops : List Op),
    (∀ o ∈ ops, legal R o) →
    Good R cap (run R cap full init ops)

def Back (R : Roles) (cap : ℕ) (ops : List Op) : Prop := Good R cap (run R cap full init ops)
def Orig (R : Roles) (cap : ℕ) (ops : List Op) : Prop := Good R cap (run R cap full init ops)

def Claim : Prop :=
  (FrozenBack = (∀ (R : Roles) (cap : ℕ) (ops : List Op),  (∀ o ∈ ops, legal R o) → Back R cap ops)) ∧
    (∀ (R : Roles) (cap : ℕ) (ops : List Op), (∀ o ∈ ops, legal R o) → (Back R cap ops ↔ Orig R cap ops))

def Witness : Prop :=
  let ops : List Op := [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .deliver 0, .arrive 0, .arrive 0]
  (∀ o ∈ ops, legal R0 o) ∧ (run R0 10 full init ops).bank = [(0, tx1)]

end PL_bg6n1_10
