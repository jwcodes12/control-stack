import ControlStack.Scenarios.SC17Drift

namespace ControlStack.SC17Drift

-- The age bound concerns birth times in the ghost drift record.
def Back_drift_lifetime : Prop :=
  ∀ (d W : ℕ) (desired : List ℕ) (ops : List Op),
    0 < W →
      let s := run d W true (init desired) ops
      ∀ p ∈ s.drift, s.clock - p.2 < W

end ControlStack.SC17Drift
