namespace PL_bg6n2_4
open ControlStack.SC26

-- "Set of messages" is expressed by membership equivalence, without
-- asserting equality of the ordering or multiplicities in the net lists.
def Back : Prop :=
  ∀ (R : Roles) (cap : ℕ) (s : St) (ops : List Op),
    s.halted = true →
    (∀ o ∈ ops, legal R o) →
    let t := run R cap full s ops
    (∀ m : ℕ × Tx, m ∈ t.net ↔ m ∈ s.net) ∧
    (∀ e ∈ t.bank, e ∈ s.bank ∨ e ∈ s.net)


def BackAt (s t : St) : Prop :=
  (∀ m : ℕ × Tx, m ∈ t.net ↔ m ∈ s.net) ∧
  (∀ e ∈ t.bank, e ∈ s.bank ∨ e ∈ s.net)
def OrigAt (s t : St) : Prop :=
  t.net = s.net ∧ (∀ e ∈ t.bank, e ∈ s.bank ∨ e ∈ s.net)
def BackEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (s : St) (ops : List Op), s.halted = true → (∀ o ∈ ops, legal R o) →
    BackAt s (run R cap full s ops)
def OrigEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (s : St) (ops : List Op), s.halted = true → (∀ o ∈ ops, legal R o) →
    OrigAt s (run R cap full s ops)
def Claim : Prop := (Back ↔ BackEnvelope) ∧
  (OrigEnvelope → Back) ∧
  (∀ (s t : St), OrigAt s t → BackAt s t) ∧
  (∃ (s t : St), s.halted = true ∧ BackAt s t ∧ ¬ OrigAt s t)
def haltedStart : St := { init with halted := true, net := [(0, tx1)] }
def Witness : Prop := haltedStart.halted = true ∧ (∀ o ∈ [Op.arrive 0], legal R0 o) ∧
  haltedStart.bank = [] ∧ haltedStart.net = [(0, tx1)] ∧
  (run R0 20 full haltedStart [.arrive 0]).bank = [(0, tx1)]
end PL_bg6n2_4
