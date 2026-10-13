namespace PL_bg2n2_6

open ControlStack ControlStack.AuditDispatch

def FrozenBack : Prop :=
∀ (s : St) (o : Op),
    (∀ id : ℕ, o ≠ Op.dispatch id) → (step s o).effects = s.effects

def BackAt (s : St) (o : Op) : Prop := (step s o).effects = s.effects
def OrigAt (s : St) (o : Op) : Prop := (step s o).effects = s.effects
def Claim : Prop := ∀ (s : St) (o : Op),
  (∀ id : ℕ, o ≠ Op.dispatch id) → (BackAt s o ↔ OrigAt s o)
def Witness : Prop := ∃ (s : St) (o : Op),
  (∀ id : ℕ, o ≠ Op.dispatch id) ∧ s.effects = [3] ∧
  (step s o).effects = [3] ∧ (step s o).requests = [4]

end PL_bg2n2_6
