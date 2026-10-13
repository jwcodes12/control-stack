namespace PL_bg3n1_7

open ControlStack
open ControlStack.SC16

def BackClosed : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (s : St) (ops : List Op),
    s.halted = true → run R h full s ops = s

def BackAt (R : Roles) (h : ℕ → ℕ) (s : St) (ops : List Op) : Prop := run R h full s ops = s
def OrigAt (R : Roles) (h : ℕ → ℕ) (s : St) (ops : List Op) : Prop := run R h full s ops = s
def OrigClosed : Prop := ∀ (R : Roles) (h : ℕ → ℕ) (s : St) (ops : List Op),
  s.halted = true → run R h full s ops = s

def Claim : Prop :=
  (BackClosed ↔ ∀ R h s ops, s.halted = true → BackAt R h s ops) ∧
  (OrigClosed ↔ ∀ R h s ops, s.halted = true → OrigAt R h s ops) ∧
  (∀ R h s ops, s.halted = true → (BackAt R h s ops ↔ OrigAt R h s ops))

def Witness : Prop :=
  let s : St := { init with halted := true, deployed := [⟨0, 5, 7⟩] }
  let ops : List Op := [.stage 1 8, .writeSlot 1 0 8, .review 2 7, .approve 3 1 7 5 0, .deploy 1 1 5 7, .halt 4]
  s.halted = true ∧ s.deployed ≠ [] ∧ run R0 id full s ops = s

end PL_bg3n1_7
