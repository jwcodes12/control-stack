import ControlStack.Scenarios.SC07Exfil

namespace ControlStack.SC07Exfil

def Back_observable_schedule_exfil : Prop :=
  ∀ q : ℕ, 0 < q →
    let b : List ℕ := [0, q, 0, q]
    let c : ℕ → ℝ := fun i => if i = 0 ∨ i = 2 then 1 else 0
    b.sum = 2 * q ∧ survive c b 0 = 1

end ControlStack.SC07Exfil
