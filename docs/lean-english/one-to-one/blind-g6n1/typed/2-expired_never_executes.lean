import ControlStack.Scenarios.SC25Audit

namespace ControlStack.SC25

def Back_expired_never_executes : Prop :=
  ∀ (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St)
    (id : ℕ) (ops : List Op),
    id ∈ s.expired →
    id ∉ s.executed.map Exec.id →
    id ∉ (run R h cls full s ops).executed.map Exec.id

end ControlStack.SC25
