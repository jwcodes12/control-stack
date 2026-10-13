-- EXCERPT of ControlStack/AuditBudget.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.AuditBudget

open Finset

/-- survival probability of attack `A` when the audit schedule is uniform over the family `𝒮` -/
noncomputable def survival {N : ℕ} (𝒮 : Finset (Finset (Fin N))) (A : Finset (Fin N)) : ℝ :=
  ((𝒮.filter (fun S => Disjoint S A)).card : ℝ) / (𝒮.card : ℝ)

/-- the uniformly random schedule: all B-subsets of the N rounds -/
def randomSchedules (N B : ℕ) : Finset (Finset (Fin N)) := powersetCard B (univ : Finset (Fin N))

end ControlStack.AuditBudget

