import ControlStack.Scenarios.SC17Drift

namespace ControlStack.SC17Drift

-- Filter the live list by nonmembership in desired; repeated entries count.
def Back_drift_bounded : Prop :=
  ∀ (d W : ℕ) (desired : List ℕ) (ops : List Op),
    0 < W →
      let s := run d W true (init desired) ops
      (s.live.filter (fun g => decide (g ∉ s.desired))).length ≤ d * W

end ControlStack.SC17Drift
