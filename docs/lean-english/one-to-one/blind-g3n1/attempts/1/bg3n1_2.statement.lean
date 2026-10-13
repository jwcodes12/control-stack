namespace PL_bg3n1_2

open ControlStack.SC15

def BackClosed : Prop :=
  ∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true → run E full s ops = s

def BackAt (E : Env) (s : St) (ops : List Op) : Prop := run E full s ops = s
def OrigAt (E : Env) (s : St) (ops : List Op) : Prop := run E full s ops = s
def OrigClosed : Prop := ∀ (E : Env) (s : St) (ops : List Op),
  s.halted = true → run E full s ops = s

def Claim : Prop :=
  (BackClosed ↔ ∀ E s ops, s.halted = true → BackAt E s ops) ∧
  (OrigClosed ↔ ∀ E s ops, s.halted = true → OrigAt E s ops) ∧
  (∀ E s ops, s.halted = true → (BackAt E s ops ↔ OrigAt E s ops))

def Witness : Prop :=
  let s : St := { init with halted := true, merged := [⟨0, 1, 7, [5], [5]⟩] }
  let ops : List Op := [.propose 1 1 8 [] [], .review 2 0 false, .runCI 0, .merge 0, .halt 9]
  s.halted = true ∧ s.merged ≠ [] ∧ run E0 full s ops = s

end PL_bg3n1_2
