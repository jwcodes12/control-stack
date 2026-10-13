namespace PL_bg4n1_8
open ControlStack.SC18Liveness

def Back_silent_ticks_halt : Prop :=
  ∀ (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (n : ℕ),
    (s.halted = false → s.clock ≤ s.lastAck + T) →
    s.lastAck + T < s.clock + n →
    (ControlStack.SC18.run admins trusted T ControlStack.SC18.full s
      (List.replicate n ControlStack.SC18.Op.tick)).halted = true

def BackAt (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (n : ℕ) : Prop :=
    (ControlStack.SC18.run admins trusted T ControlStack.SC18.full s (List.replicate n ControlStack.SC18.Op.tick)).halted = true

def OrigAt (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (n : ℕ) : Prop :=
    (ControlStack.SC18.run admins trusted T ControlStack.SC18.full s (List.replicate n ControlStack.SC18.Op.tick)).halted = true

def Claim : Prop :=
  (Back_silent_ticks_halt ↔ ∀ (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (n : ℕ), (s.halted = false → s.clock ≤ s.lastAck + T) → s.lastAck + T < s.clock + n → BackAt admins trusted T s n) ∧
  (∀ (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (n : ℕ), (s.halted = false → s.clock ≤ s.lastAck + T) → s.lastAck + T < s.clock + n → (BackAt admins trusted T s n ↔ OrigAt admins trusted T s n))

def Witness : Prop :=
    let s := ControlStack.SC18.init 0
    (s.halted = false → s.clock ≤ s.lastAck + 2) ∧ s.lastAck + 2 < s.clock + 3 ∧
    (ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full s (List.replicate 3 ControlStack.SC18.Op.tick)).halted = true ∧
    (ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full s (List.replicate 3 ControlStack.SC18.Op.tick)).clock = 3

end PL_bg4n1_8
