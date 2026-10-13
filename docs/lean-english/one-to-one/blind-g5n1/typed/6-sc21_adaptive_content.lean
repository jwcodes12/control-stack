import ControlStack.Scenarios.EvalIntegrityAdaptive
import ControlStack.Families.F6.ReservedAudit

namespace ControlStack.EvalIntegrityAdaptive

open ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert
open ControlStack.ReservedAudit
open scoped BigOperators

-- NOTE
-- NOT_FORMALISABLE: If "arbitrary hidden component" includes infinite
-- hidden types, the supplied val has no counterpart for them: it requires
-- Fintype Y. This best effort covers every finite hidden type. The visible
-- output remains the corruption bit, a Unit placeholder, and a catch bit,
-- as in claim 5. No consistency of catch bits with S is added; the event
-- itself requires both disjointness and absence of all catches.
def Back_sc21_adaptive_content : Prop :=
  ∀ (N B k : ℕ) (Y : Type) [Fintype Y]
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ),
    B ≤ N →
    (∀ g, IsDist (σ g)) →
    (∀ S ∈ randomSchedules N B, ∀ h yo, 0 ≤ K S h yo) →
    (∀ S ∈ randomSchedules N B, ∀ h,
      (∑ y, ∑ o, K S h (y, o)) ≤ 1) →
    (∀ S ∈ randomSchedules N B, ∀ h a,
      (∑ y, ∑ f : Bool, K S h (y, (a, (), f))) ≤
        σ (h.map Prod.snd) a) →
    (∑ S ∈ randomSchedules N B,
      (Nat.choose N B : ℝ)⁻¹ * val (K S) (successInd k S) N []) ≤
      (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)

end ControlStack.EvalIntegrityAdaptive
