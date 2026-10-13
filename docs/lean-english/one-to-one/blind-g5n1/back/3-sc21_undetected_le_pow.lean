import ControlStack.Scenarios.EvalIntegrity

namespace ControlStack.EvalIntegrity

open ControlStack.AuditBudget

def Back_sc21_undetected_le_pow : Prop :=
  ∀ (N B k : ℕ) (rep truth : Fin N → ℕ),
    0 < N → B ≤ N → (corrupt rep truth).card = k →
    survival (randomSchedules N B) (corrupt rep truth) ≤
      (((N - B : ℕ) : ℝ) / (N : ℝ)) ^ k

end ControlStack.EvalIntegrity
