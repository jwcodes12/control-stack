namespace ControlStack.SC18Liveness

def Back_progress_interleaved : Prop :=
  ∀ (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (i : ℕ)
    (a0 a1 a2 a3 : List ControlStack.SC18.Op),
    let beforeLog := ControlStack.SC18.run admins trusted T ControlStack.SC18.full s
      (a0 ++ [.request i] ++ a1)
    let final := ControlStack.SC18.run admins trusted T ControlStack.SC18.full s
      (a0 ++ [.request i] ++ a1 ++ [.logWrite i] ++ a2 ++ [.release i] ++ a3)
    i ∈ final.released.map ControlStack.SC18.Rel.id ∨
      final.halted = true ∨ beforeLog.sinkUp = false

end ControlStack.SC18Liveness
