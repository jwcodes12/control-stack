namespace PL_bg4n1_6
open ControlStack.SC18Liveness

def Back_honest_release : Prop :=
  ∀ (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (i : ℕ),
    s.halted = false → s.sinkUp = true →
    i ∈ (ControlStack.SC18.run admins trusted T ControlStack.SC18.full s
      [.request i, .logWrite i, .release i]).released.map ControlStack.SC18.Rel.id

def BackAt (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (i : ℕ) : Prop :=
    i ∈ (ControlStack.SC18.run admins trusted T ControlStack.SC18.full s [.request i, .logWrite i, .release i]).released.map ControlStack.SC18.Rel.id

def OrigAt (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (i : ℕ) : Prop :=
    i ∈ (ControlStack.SC18.run admins trusted T ControlStack.SC18.full s [.request i, .logWrite i, .release i]).released.map ControlStack.SC18.Rel.id

def Claim : Prop :=
  (Back_honest_release ↔ ∀ (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (i : ℕ), s.halted = false → s.sinkUp = true → BackAt admins trusted T s i) ∧
  (∀ (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (i : ℕ), s.halted = false → s.sinkUp = true → (BackAt admins trusted T s i ↔ OrigAt admins trusted T s i))

def Witness : Prop :=
    let s := ControlStack.SC18.init 66
    let t := ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full s [.request 0, .logWrite 0, .release 0]
    let old : ControlStack.SC18.St := { ControlStack.SC18.init 0 with released := [⟨0, 0, 100, 0⟩] }
    let oldFinal := ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full old [.request 0, .logWrite 0, .release 0]
    s.halted = false ∧ s.sinkUp = true ∧ t.released = [⟨0, 0, 0, 0⟩] ∧ t.logged = [] ∧
    ¬ ControlStack.SC18.Good 2 t ∧ old.halted = false ∧ old.sinkUp = true ∧
    oldFinal.released = old.released ∧ 0 ∈ oldFinal.released.map ControlStack.SC18.Rel.id ∧
    ¬ ControlStack.SC18.Good 2 oldFinal

end PL_bg4n1_6
