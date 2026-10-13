namespace PL_bg2n2_8

open ControlStack ControlStack.SC14

def FrozenBack : Prop :=
∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true → (run E full s ops).usage = s.usage

def BackAt (E : Env) (s : St) (ops : List Op) : Prop := (run E full s ops).usage = s.usage
def OrigAt (E : Env) (s : St) (ops : List Op) : Prop := (run E full s ops).usage = s.usage
def Claim : Prop := ∀ (E : Env) (s : St) (ops : List Op),
  s.halted = true → (BackAt E s ops ↔ OrigAt E s ops)
def Witness : Prop := ∃ (s : St) (ops : List Op),
  s.halted = true ∧ s.usage = [((2, 2, 2), 0, 100)] ∧ s.spent = (2, 2, 2) ∧
  Op.rollback ∈ ops ∧ (run E0 full s ops).spent = 0 ∧ (run E0 full s ops).usage = s.usage

end PL_bg2n2_8
