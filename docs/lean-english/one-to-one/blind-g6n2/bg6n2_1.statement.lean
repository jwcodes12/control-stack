namespace PL_bg6n2_1
open ControlStack.SC26

-- The nonce and haltCheck flags are unrestricted by Sound.
def Back : Prop :=
  ∀ (R : Roles) (cap : ℕ) (C : Checks) (ops : List Op),
    Sound C →
    (∀ o ∈ ops, legal R o) →
    Good R cap (run R cap C init ops)


def BackAt (R : Roles) (cap : ℕ) (s : St) : Prop := Good R cap s
def OrigAt (R : Roles) (cap : ℕ) (s : St) : Prop := Good R cap s
def BackEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (C : Checks) (ops : List Op), Sound C → (∀ o ∈ ops, legal R o) →
    BackAt R cap (run R cap C init ops)
def OrigEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (C : Checks) (ops : List Op), Sound C → (∀ o ∈ ops, legal R o) →
    OrigAt R cap (run R cap C init ops)
def Claim : Prop := (Back ↔ BackEnvelope) ∧ (∀ (R : Roles) (cap : ℕ) (s : St), BackAt R cap s ↔ OrigAt R cap s)
def honestOps : List Op := [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .deliver 0, .arrive 0]
def Witness : Prop := Sound full ∧ (∀ o ∈ honestOps, legal R0 o) ∧
  (run R0 20 full init honestOps).bank = [(0, tx1)]
end PL_bg6n2_1
