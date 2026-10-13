namespace ControlStack.SC18Liveness

def Back_honest_release : Prop :=
  ∀ (admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (i : ℕ),
    s.halted = false → s.sinkUp = true →
    i ∈ (ControlStack.SC18.run admins trusted T ControlStack.SC18.full s
      [.request i, .logWrite i, .release i]).released.map ControlStack.SC18.Rel.id

end ControlStack.SC18Liveness
