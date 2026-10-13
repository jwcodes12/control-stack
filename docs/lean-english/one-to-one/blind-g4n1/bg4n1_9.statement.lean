namespace PL_bg4n1_9
open ControlStack.SC18Liveness.Resume

def Back_resume_safe : Prop :=
  ∀ (admins : List ℕ) (T : ℕ) (ops : List Op),
    let final := run admins T init ops
    (∀ r ∈ final.released, RelOk T final r) ∧
      (final.released.map ControlStack.SC18.Rel.id).Nodup

def BackAt (admins : List ℕ) (T : ℕ) (ops : List Op) : Prop :=
    let final := run admins T init ops
    (∀ r ∈ final.released, RelOk T final r) ∧ (final.released.map ControlStack.SC18.Rel.id).Nodup

def OrigAt (admins : List ℕ) (T : ℕ) (ops : List Op) : Prop :=
    (∀ r ∈ (run admins T init ops).released, RelOk T (run admins T init ops) r) ∧ ((run admins T init ops).released.map ControlStack.SC18.Rel.id).Nodup

def Claim : Prop :=
  (Back_resume_safe ↔ ∀ (admins : List ℕ) (T : ℕ) (ops : List Op),  BackAt admins T ops) ∧
  (∀ (admins : List ℕ) (T : ℕ) (ops : List Op),  (BackAt admins T ops ↔ OrigAt admins T ops))

def Witness : Prop :=
    let pausedOps : List Op := [.request 0, .logWrite 0, .sinkDown, .tick, .tick, .tick, .release 0]
    let resumedOps := pausedOps ++ [.sinkRestore, .logWrite 0, .release 0]
    (run [9] 2 init pausedOps).released = [] ∧ (run [9] 2 init pausedOps).paused = true ∧
    (run [9] 2 init resumedOps).released = [⟨0, 2, 3, 3⟩] ∧
    BackAt [9] 2 resumedOps

end PL_bg4n1_9
