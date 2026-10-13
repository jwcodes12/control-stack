namespace PL_bg4n1_10
open ControlStack.SC18Liveness.Resume

def Back_resume_progress : Prop :=
  ∀ (admins : List ℕ) (T : ℕ) (s : St) (i : ℕ),
    s.halted = false → s.sinkUp = true → i ∈ s.reqs →
    i ∈ (run admins T s [.logWrite i, .release i]).released.map ControlStack.SC18.Rel.id

def BackAt (admins : List ℕ) (T : ℕ) (s : St) (i : ℕ) : Prop :=
    i ∈ (run admins T s [.logWrite i, .release i]).released.map ControlStack.SC18.Rel.id

def OrigAt (admins : List ℕ) (T : ℕ) (s : St) (i : ℕ) : Prop :=
    i ∈ (run admins T s [.logWrite i, .release i]).released.map ControlStack.SC18.Rel.id

def Claim : Prop :=
  (Back_resume_progress ↔ ∀ (admins : List ℕ) (T : ℕ) (s : St) (i : ℕ), s.halted = false → s.sinkUp = true → i ∈ s.reqs → BackAt admins T s i) ∧
  (∀ (admins : List ℕ) (T : ℕ) (s : St) (i : ℕ), s.halted = false → s.sinkUp = true → i ∈ s.reqs → (BackAt admins T s i ↔ OrigAt admins T s i))

def Witness : Prop :=
    let s : St := { init with reqs := [0], paused := true, clock := 10 }
    let old : St := { s with released := [⟨0, 0, 100, 0⟩] }
    let t := run [9] 2 s [.logWrite 0, .release 0]
    let oldFinal := run [9] 2 old [.logWrite 0, .release 0]
    s.halted = false ∧ s.sinkUp = true ∧ 0 ∈ s.reqs ∧ s.paused = true ∧
    t.released = [⟨0, 1, 10, 10⟩] ∧ t.paused = false ∧
    old.halted = false ∧ old.sinkUp = true ∧ 0 ∈ old.reqs ∧
    oldFinal.released = old.released ∧ 0 ∈ oldFinal.released.map ControlStack.SC18.Rel.id ∧
    ¬ RelOk 2 oldFinal ⟨0, 0, 100, 0⟩

end PL_bg4n1_10
