import ControlStack.Scenarios.EvalIntegrityAdaptive
import ControlStack.Families.F6.ReservedRecall

namespace ControlStack.EvalIntegrityAdaptive

open ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert
open ControlStack.ReservedRecall
open scoped BigOperators

-- NOTE
-- NOT_FORMALISABLE: As in claim 6, the supplied expectation val supports
-- finite hidden types only. The best effort below quantifies over every
-- finite Y. Recall is imposed at every full history through the joint
-- no-catch marginal bound, without assuming independent detection events.
def Back_sc21_adaptive_recall : Prop :=
  ∀ (N B k : ℕ) (r : ℝ) (Y : Type) [Fintype Y]
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ),
    B ≤ N → 0 ≤ r → r ≤ 1 →
    (∀ g, IsDist (σ g)) →
    (∀ S ∈ randomSchedules N B, ∀ h yo, 0 ≤ K S h yo) →
    (∀ S ∈ randomSchedules N B, ∀ h,
      (∑ y, ∑ o, K S h (y, o)) ≤ 1) →
    (∀ S ∈ randomSchedules N B, ∀ h a,
      (∑ y, ∑ f : Bool, K S h (y, (a, (), f))) ≤
        σ (h.map Prod.snd) a) →
    (∀ S ∈ randomSchedules N B, ∀ h a,
      (∑ y, K S h (y, (a, (), false))) ≤
        σ (h.map Prod.snd) a *
          (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) →
    (∑ S ∈ randomSchedules N B,
      (Nat.choose N B : ℝ)⁻¹ * val (K S) (recallSucc (N := N) k) N []) ≤
      hypMiss N B k r

end ControlStack.EvalIntegrityAdaptive
