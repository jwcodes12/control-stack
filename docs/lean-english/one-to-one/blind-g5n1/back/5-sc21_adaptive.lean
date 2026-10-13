import ControlStack.Scenarios.EvalIntegrityAdaptive

namespace ControlStack.EvalIntegrityAdaptive

open ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert
open scoped BigOperators

def Back_sc21_adaptive : Prop :=
  ∀ (N B k : ℕ) (σ : List (AOut Unit) → Bool → ℝ),
    B ≤ N → (∀ g, IsDist (σ g)) →
    (∑ S ∈ randomSchedules N B,
      (Nat.choose N B : ℝ)⁻¹ *
        val (hiddenK (N := N) σ S) (survInd k S) N []) ≤
      (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)

end ControlStack.EvalIntegrityAdaptive
