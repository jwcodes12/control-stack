namespace PL_bg6n1_1

open ControlStack.SC25

def FrozenBack : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op),
    Good R h cls (run R h cls full init ops)

def Back (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) : Prop := Good R h cls (run R h cls full init ops)
def Orig (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) : Prop := Good R h cls (run R h cls full init ops)

def Claim : Prop :=
  (FrozenBack = (∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op), Back R h cls ops)) ∧
    (∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op), (Back R h cls ops ↔ Orig R h cls ops))

def Witness : Prop :=
  (run R0 id cls0 full init [.submit 1 0 100 true, .audit 2 0 true, .approve 3 0, .check 0, .crash, .check 0, .fire 0]).executed.map Exec.content = [100]

end PL_bg6n1_1
