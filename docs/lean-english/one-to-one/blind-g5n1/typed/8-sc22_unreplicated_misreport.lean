import ControlStack.Scenarios.EvalIntegrity

namespace ControlStack.EvalIntegrity

open ControlStack.AuditBudget

-- NOTE
-- AMBIGUOUS: As in claim 2, B ≤ N is not stated. For B > N a uniform
-- size-B sample does not exist. This uses the supplied totalized survival
-- ratio, which gives zero on an empty family. Findings are numerical
-- reports, with exactly the same corrupt set as in claim 2.
def Back_sc22_unreplicated_misreport : Prop :=
  ∀ (N B k : ℕ) (rep truth : Fin N → ℕ),
    (corrupt rep truth).card = k →
    survival (randomSchedules N B) (corrupt rep truth) =
      (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)

end ControlStack.EvalIntegrity
