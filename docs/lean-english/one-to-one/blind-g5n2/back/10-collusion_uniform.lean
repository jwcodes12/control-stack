import ControlStack.Families.F6.MonitorCollusion

namespace ControlStack.MonitorCollusion

open ControlStack.Covert

-- P is the real-attack law, Q is the honeypot law; true means pass and
-- false means flag. The division by 2 fixes the phase prior to be uniform.
def Back_collusion_uniform : Prop :=
  ∀ (V : Type) [Fintype V] (P Q : V → ℝ) (monitor : V → Bool → ℝ),
    IsDist P → IsDist Q →
      (∀ v, IsDist (monitor v)) →
        (passRate P (fun v => monitor v true) +
          passRate Q (fun v => monitor v false)) / 2 ≤
            (1 + tv P Q) / 2

end ControlStack.MonitorCollusion
