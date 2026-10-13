import ControlStack.Scenarios.SC28Budget

namespace ControlStack.SC28

def Back_revoked_lease_stops : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (C : Checks) (s : St)
    (lid : ℕ) (ops : List Op),
    lid ∈ s.revoked →
    usedL (run admins G C s ops) lid = usedL s lid

end ControlStack.SC28
