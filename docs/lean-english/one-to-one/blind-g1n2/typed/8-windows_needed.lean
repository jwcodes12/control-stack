import ControlStack.Scenarios.SC07Exfil

namespace ControlStack.SC07Exfil

def Back_windows_needed : Prop :=
  ∀ (S q : ℕ) (b : List ℕ),
    0 < q →
    (∀ x ∈ b, x ≤ q) →
    S ≤ b.sum →
    ceilDiv S q ≤ traffic b

end ControlStack.SC07Exfil
