import ControlStack.Scenarios.EvalIntegrity

namespace ControlStack.EvalIntegrity

open ControlStack.AuditBudget

-- NOTE
-- AMBIGUOUS: No B ≤ N hypothesis is stated. For B > N there is no
-- uniform distribution on size-B subsets. The proposition below uses the
-- supplied survival definition, whose empty-family ratio is totalized
-- to zero by real division in Lean; it agrees with the stated probability
-- whenever size-B samples exist.
def Back_sc21_undetected_prob : Prop :=
  ∀ (N B k : ℕ) (rep truth : Fin N → ℕ),
    (corrupt rep truth).card = k →
    survival (randomSchedules N B) (corrupt rep truth) =
      (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)

end ControlStack.EvalIntegrity
