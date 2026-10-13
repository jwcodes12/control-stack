namespace PL_bg4n1_1
open ControlStack.SC18

def Back_sc18_safe : Prop :=
  ∀ (admins : List ℕ) (trusted T : ℕ) (ops : List Op),
    (∀ o ∈ ops, legal admins trusted o) →
    Good T (run admins trusted T full (init trusted) ops)

def BackAt (admins : List ℕ) (trusted T : ℕ) (ops : List Op) : Prop :=
    Good T (run admins trusted T full (init trusted) ops)

def OrigAt (admins : List ℕ) (trusted T : ℕ) (ops : List Op) : Prop :=
    Good T (run admins trusted T full (init trusted) ops)

def Claim : Prop :=
  (Back_sc18_safe ↔ ∀ (admins : List ℕ) (trusted T : ℕ) (ops : List Op), (∀ o ∈ ops, legal admins trusted o) → BackAt admins trusted T ops) ∧
  (∀ (admins : List ℕ) (trusted T : ℕ) (ops : List Op), (∀ o ∈ ops, legal admins trusted o) → (BackAt admins trusted T ops ↔ OrigAt admins trusted T ops))

def Witness : Prop :=
    let ops : List Op := [.request 0, .logWrite 0, .tick, .release 0]
    (∀ o ∈ ops, legal [9] 0 o) ∧
    (run [9] 0 2 full (init 0) ops).released = [⟨0, 1, 1, 0⟩] ∧
    Good 2 (run [9] 0 2 full (init 0) ops)

end PL_bg4n1_1
