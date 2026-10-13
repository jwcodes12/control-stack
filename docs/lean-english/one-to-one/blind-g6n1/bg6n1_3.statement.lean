namespace PL_bg6n1_3

open ControlStack.SC25

def FrozenBack : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St)
    (ops : List Op),
    s.halted = true →
    (run R h cls full s ops).executed = s.executed

def Back (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (ops : List Op) : Prop := (run R h cls full s ops).executed = s.executed
def Orig (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (ops : List Op) : Prop := (run R h cls full s ops).executed = s.executed

def Claim : Prop :=
  (FrozenBack = (∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (ops : List Op), s.halted = true → Back R h cls s ops)) ∧
    (∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (ops : List Op), s.halted = true → (Back R h cls s ops ↔ Orig R h cls s ops))

def Witness : Prop :=
  let s := run R0 id cls0 full init ([.submit 1 0 7 false, .audit 2 0 true, .check 0, .fire 0] ++ [.halt 4])
  s.halted = true ∧ s.executed.map Exec.content = [7] ∧
    (run R0 id cls0 full s [.crash, .amend 1 0 50, .audit 2 0 false, .fire 0, .halt 4]).executed = s.executed

end PL_bg6n1_3
