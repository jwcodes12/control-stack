namespace PL_bg4n1_2
open ControlStack.SC18

def Back_config_untampered : Prop :=
  ∀ (admins : List ℕ) (trusted T : ℕ) (ops : List Op),
    (∀ o ∈ ops, legal admins trusted o) →
    (run admins trusted T full (init trusted) ops).cfg = trusted

def BackAt (admins : List ℕ) (trusted T : ℕ) (ops : List Op) : Prop :=
    (run admins trusted T full (init trusted) ops).cfg = trusted

def OrigAt (admins : List ℕ) (trusted T : ℕ) (ops : List Op) : Prop :=
    (run admins trusted T full (init trusted) ops).cfg = trusted

def Claim : Prop :=
  (Back_config_untampered ↔ ∀ (admins : List ℕ) (trusted T : ℕ) (ops : List Op), (∀ o ∈ ops, legal admins trusted o) → BackAt admins trusted T ops) ∧
  (∀ (admins : List ℕ) (trusted T : ℕ) (ops : List Op), (∀ o ∈ ops, legal admins trusted o) → (BackAt admins trusted T ops ↔ OrigAt admins trusted T ops))

def Witness : Prop :=
    let ops : List Op := [.setSink 1 66, .setSink 9 0, .request 0, .logWrite 0, .release 0]
    (∀ o ∈ ops, legal [9] 0 o) ∧
    (run [9] 0 2 full (init 0) ops).cfg = 0 ∧
    (run [9] 0 2 full (init 0) ops).released.map Rel.id = [0]

end PL_bg4n1_2
