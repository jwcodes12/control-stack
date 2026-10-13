namespace PL_bg2n2_5

open ControlStack ControlStack.AuditDispatch

def FrozenBack : Prop :=
∀ (s : St) (ops : List Op),
    Inv s → Inv (run s ops) ∧ s.audits <+: (run s ops).audits

def BackAt (s : St) (ops : List Op) : Prop := Inv (run s ops) ∧ s.audits <+: (run s ops).audits
def OrigAt (s : St) (ops : List Op) : Prop := Inv (run s ops) ∧ s.audits <+: (run s ops).audits
def Claim : Prop := ∀ (s : St) (ops : List Op), Inv s → (BackAt s ops ↔ OrigAt s ops)
def Witness : Prop := ∃ (s : St) (ops : List Op),
  Inv s ∧ s.effects = [1] ∧ ops ≠ [] ∧
  (run s ops).audits = [1, 2] ∧ (run s ops).effects = [1, 2]

end PL_bg2n2_5
