import ControlStack.Families.F6.MonitorCollusion

namespace ControlStack.MonitorCollusion

open ControlStack.Covert

def Back_pass_transfer : Prop :=
  ∀ (V : Type) [Fintype V] (P Q β : V → ℝ),
    IsDist P → IsDist Q →
      (∀ v, 0 ≤ β v ∧ β v ≤ 1) →
        |passRate P β - passRate Q β| ≤ tv P Q

end ControlStack.MonitorCollusion
