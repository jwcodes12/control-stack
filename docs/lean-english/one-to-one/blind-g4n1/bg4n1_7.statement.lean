namespace PL_bg4n1_7
open ControlStack.SC18Liveness

def Back_progress_interleaved : Prop :=
  ∀ (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (i : ℕ)
    (a0 a1 a2 a3 : List ControlStack.SC18.Op),
    let beforeLog := ControlStack.SC18.run admins trusted T ControlStack.SC18.full s
      (a0 ++ [.request i] ++ a1)
    let final := ControlStack.SC18.run admins trusted T ControlStack.SC18.full s
      (a0 ++ [.request i] ++ a1 ++ [.logWrite i] ++ a2 ++ [.release i] ++ a3)
    i ∈ final.released.map ControlStack.SC18.Rel.id ∨
      final.halted = true ∨ beforeLog.sinkUp = false

def BackAt (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (i : ℕ) (a0 a1 a2 a3 : List ControlStack.SC18.Op) : Prop :=
    let beforeLog := ControlStack.SC18.run admins trusted T ControlStack.SC18.full s (a0 ++ [.request i] ++ a1)
    let final := ControlStack.SC18.run admins trusted T ControlStack.SC18.full s (a0 ++ [.request i] ++ a1 ++ [.logWrite i] ++ a2 ++ [.release i] ++ a3)
    i ∈ final.released.map ControlStack.SC18.Rel.id ∨ final.halted = true ∨ beforeLog.sinkUp = false

def OrigAt (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (i : ℕ) (a0 a1 a2 a3 : List ControlStack.SC18.Op) : Prop :=
    let t := ControlStack.SC18.run admins trusted T ControlStack.SC18.full s (a0 ++ .request i :: a1 ++ .logWrite i :: a2 ++ .release i :: a3)
    i ∈ t.released.map ControlStack.SC18.Rel.id ∨ t.halted = true ∨
      (ControlStack.SC18.run admins trusted T ControlStack.SC18.full (ControlStack.SC18.step admins trusted T ControlStack.SC18.full (ControlStack.SC18.run admins trusted T ControlStack.SC18.full s a0) (.request i)) a1).sinkUp = false

def Claim : Prop :=
  (Back_progress_interleaved ↔ ∀ (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (i : ℕ) (a0 a1 a2 a3 : List ControlStack.SC18.Op),  BackAt admins trusted T s i a0 a1 a2 a3) ∧
  (∀ (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (i : ℕ) (a0 a1 a2 a3 : List ControlStack.SC18.Op),  (BackAt admins trusted T s i a0 a1 a2 a3 ↔ OrigAt admins trusted T s i a0 a1 a2 a3))

def Witness : Prop :=
    let s := ControlStack.SC18.init 0
    let t := ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full s
      ([.setSink 1 66] ++ [.request 0] ++ [.tick] ++ [.logWrite 0] ++ [.sinkDown] ++ [.release 0] ++ [.sinkRestore])
    let halted := ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full s [.halt 9, .request 0, .logWrite 0, .release 0]
    let down := ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full s [.request 0, .sinkDown, .logWrite 0, .release 0]
    let outage := ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full s [.request 0, .logWrite 0, .sinkDown, .release 0]
    outage.sinkUp = false ∧ outage.released.map ControlStack.SC18.Rel.id = [0] ∧
    t.released.map ControlStack.SC18.Rel.id = [0] ∧ t.halted = false ∧
    halted.released = [] ∧ halted.halted = true ∧
    down.released = [] ∧ down.halted = false ∧
    (ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full s [.request 0, .sinkDown]).sinkUp = false

end PL_bg4n1_7
