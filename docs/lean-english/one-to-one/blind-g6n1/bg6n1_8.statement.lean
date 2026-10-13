namespace PL_bg6n1_8

open ControlStack.SC25Refinement ControlStack.SC25

def FrozenBack : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp),
    Good R h cls (α (runC R h cls false cinit ops))

def Back (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp) : Prop := Good R h cls (α (runC R h cls false cinit ops))
def Orig (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp) : Prop := Good R h cls (α (runC R h cls false cinit ops))

def Claim : Prop :=
  (FrozenBack = (∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp), Back R h cls ops)) ∧
    (∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp), (Back R h cls ops ↔ Orig R h cls ops))

def Witness : Prop :=
  (runC R0 id cls0 false cinit [.submit 1 0 7 false, .audit 2 0 true, .fire 0, .submit 1 1 100 true, .audit 2 1 true, .approve 3 1, .crash, .restart, .fire 1]).effects.map ERow.content = [7, 100]

end PL_bg6n1_8
