namespace PL_bg3n2_2
open ControlStack.SC16Refinement ControlStack
open ControlStack.SC16

def BackClosed : Prop :=
  ∀ (R : SC16.Roles) (h : ℕ → ℕ) (ops : List COp),
    SC16.Good R h (α (runC R h false cinit ops))

def BackAt (R : Roles) (h : ℕ → ℕ) (ops : List COp) : Prop :=
  SC16.Good R h (α (runC R h false cinit ops))
def OrigAt (R : Roles) (h : ℕ → ℕ) (ops : List COp) : Prop :=
  Good R h (α (runC R h false cinit ops))

def OrigClosed : Prop := ∀ R h ops, OrigAt R h ops
def OriginalDeclaration : OrigClosed := @ControlStack.SC16Refinement.concrete_safe

def Claim : Prop :=
  (BackClosed ↔ ∀ R h ops, BackAt R h ops) ∧
  (∀ R h ops, BackAt R h ops ↔ OrigAt R h ops)

def Witness : Prop :=
  (α (runC R0 id false cinit [.put 1 7, .review 2 7 5, .approve 3 0 7 5 0, .deploy 1 0 5])).deployed = [⟨0, 5, 7⟩] ∧
  OrigAt R0 id [.put 1 7, .review 2 7 5, .approve 3 0 7 5 0, .deploy 1 0 5]

end PL_bg3n2_2
