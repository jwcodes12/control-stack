namespace PL_bg6n2_6
open ControlStack.SC26
open ControlStack.SC26Refinement

open ControlStack.SC26

def Back : Prop :=
  ∀ (R : Roles) (cap : ℕ) (s : CSt) (ops : List COp),
    s.halted = true →
    (∀ o ∈ ops, legalC R o) →
    let t := runC R cap true s ops
    t.wire = s.wire ∧
    (∀ e ∈ t.bank, e ∈ s.bank ∨ e ∈ s.wire)


def BackAt (s t : CSt) : Prop :=
  t.wire = s.wire ∧ (∀ e ∈ t.bank, e ∈ s.bank ∨ e ∈ s.wire)
def OrigAt (s t : CSt) : Prop :=
  t.wire = s.wire ∧ (∀ e ∈ t.bank, e ∈ s.bank ∨ e ∈ s.wire)
def BackEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (s : CSt) (ops : List COp), s.halted = true → (∀ o ∈ ops, legalC R o) →
    BackAt s (runC R cap true s ops)
def OrigEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (s : CSt) (ops : List COp), s.halted = true → (∀ o ∈ ops, legalC R o) →
    OrigAt s (runC R cap true s ops)
def Claim : Prop := (Back ↔ BackEnvelope) ∧ (∀ (s t : CSt), BackAt s t ↔ OrigAt s t)
def haltedCStart : CSt := { cinit with halted := true, wire := [(0, tx1)] }
def Witness : Prop := haltedCStart.halted = true ∧ (∀ o ∈ [COp.bankProcess 0], legalC R0 o) ∧
  haltedCStart.bank = [] ∧ haltedCStart.wire = [(0, tx1)] ∧
  (runC R0 20 true haltedCStart [.bankProcess 0]).bank = [(0, tx1)]
end PL_bg6n2_6
