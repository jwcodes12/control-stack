namespace PL_bg4n1_3
open ControlStack.SC18

def Back_halt_freezes : Prop :=
  ∀ (admins : List ℕ) (trusted T : ℕ) (s : St) (ops : List Op),
    s.halted = true →
    (run admins trusted T full s ops).released = s.released

def BackAt (admins : List ℕ) (trusted T : ℕ) (s : St) (ops : List Op) : Prop :=
    (run admins trusted T full s ops).released = s.released

def OrigAt (admins : List ℕ) (trusted T : ℕ) (s : St) (ops : List Op) : Prop :=
    (run admins trusted T full s ops).released = s.released

def Claim : Prop :=
  (Back_halt_freezes ↔ ∀ (admins : List ℕ) (trusted T : ℕ) (s : St) (ops : List Op), s.halted = true → BackAt admins trusted T s ops) ∧
  (∀ (admins : List ℕ) (trusted T : ℕ) (s : St) (ops : List Op), s.halted = true → (BackAt admins trusted T s ops ↔ OrigAt admins trusted T s ops))

def Witness : Prop :=
    let s : St := { init 0 with halted := true, clock := 7, released := [⟨0, 1, 0, 0⟩] }
    let ops : List Op := [.tick, .sinkDown, .request 1, .logWrite 1, .release 1]
    s.halted = true ∧ (run [9] 0 2 full s ops).released = s.released ∧
    (run [9] 0 2 full s ops).clock = 7 ∧ (run [9] 0 2 full s ops).sinkUp = false ∧
    step [9] 0 2 full s .tick = s

end PL_bg4n1_3
