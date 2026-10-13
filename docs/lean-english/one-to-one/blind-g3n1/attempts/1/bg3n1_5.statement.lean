namespace PL_bg3n1_5

open ControlStack.SC16

def BackClosed : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (ops : List Op),
    Good R h (run R h full init ops)

def BackAt (R : Roles) (h : ℕ → ℕ) (s : St) : Prop := Good R h s
def OrigAt (R : Roles) (h : ℕ → ℕ) (s : St) : Prop := Good R h s
def OrigClosed : Prop := ∀ (R : Roles) (h : ℕ → ℕ) (ops : List Op), Good R h (run R h full init ops)

def Claim : Prop :=
  (BackClosed ↔ ∀ R h ops, BackAt R h (run R h full init ops)) ∧
  (OrigClosed ↔ ∀ R h ops, OrigAt R h (run R h full init ops)) ∧
  (∀ R h s, BackAt R h s ↔ OrigAt R h s)

def Witness : Prop :=
  let s := run R0 id full init [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]
  s.deployed = [⟨0, 5, 7⟩] ∧ s.reviews ≠ [] ∧ s.approvals ≠ []

end PL_bg3n1_5
