import ControlStack.Scenarios.SC07Exfil
import ControlStack.CovertChannel

open scoped BigOperators
open Classical

namespace ControlStack.SC07Exfil

def Back_sc07_mixed : Prop :=
  ∀ (P : Type) [Fintype P] (S q : ℕ) (pr : ℝ)
      (plans : P → List ℕ) (w : P → ℝ) (c : ℕ → ℝ),
    0 < q →
    0 ≤ pr → pr ≤ 1 →
    (∀ i, pr ≤ c i) →
    (∀ i, c i ≤ 1) →
    ControlStack.Covert.IsDist w →
    (∑ p, if S ≤ (capped q (plans p)).sum
      then w p * survive c (capped q (plans p)) 0 else 0) ≤
      (1 - pr) ^ ceilDiv S q

end ControlStack.SC07Exfil
