import ControlStack.Scenarios.SC18Liveness

namespace ControlStack.SC18Liveness.Resume

def Back_resume_safe : Prop :=
  ∀ (admins : List ℕ) (T : ℕ) (ops : List Op),
    let final := run admins T init ops
    (∀ r ∈ final.released, RelOk T final r) ∧
      (final.released.map ControlStack.SC18.Rel.id).Nodup

end ControlStack.SC18Liveness.Resume
