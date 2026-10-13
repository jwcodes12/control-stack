namespace PL_bg2n2_2

open ControlStack ControlStack.SC12

def FrozenBack : Prop :=
∀ (admins : List ℕ) (s : St) (ops : List Op),
    s.halted = true → run admins full s ops = s

def BackAt (admins : List ℕ) (s : St) (ops : List Op) : Prop := run admins full s ops = s
def OrigAt (admins : List ℕ) (s : St) (ops : List Op) : Prop := run admins full s ops = s
def Claim : Prop := ∀ (admins : List ℕ) (s : St) (ops : List Op),
  s.halted = true → (BackAt admins s ops ↔ OrigAt admins s ops)
def Witness : Prop := ∃ (s : St) (ops : List Op),
  s.halted = true ∧ s.fired = [(5, 1, 0)] ∧ ops ≠ [] ∧ run [9] full s ops = s

end PL_bg2n2_2
