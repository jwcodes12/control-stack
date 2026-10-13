import ControlStack.Scenarios.SC18Liveness

namespace ControlStack.SC18Liveness.Resume

def Back_resume_progress : Prop :=
  ∀ (admins : List ℕ) (T : ℕ) (s : St) (i : ℕ),
    s.halted = false → s.sinkUp = true → i ∈ s.reqs →
    i ∈ (run admins T s [.logWrite i, .release i]).released.map ControlStack.SC18.Rel.id

end ControlStack.SC18Liveness.Resume
