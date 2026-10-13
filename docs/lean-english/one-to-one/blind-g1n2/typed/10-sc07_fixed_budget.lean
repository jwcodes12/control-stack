import ControlStack.Scenarios.SC07Exfil
import ControlStack.Families.F6.ReservedRecall

open scoped BigOperators
open Classical
open ControlStack.Covert ControlStack.Leakage

namespace ControlStack.SC07Exfil

-- NOTE
-- AMBIGUOUS: The batch calls sigma the attacker's "own traffic law" but
-- does not explicitly state its normalization. Here each visible-history
-- row is a nonnegative sub-probability law on Bool, allowing lost mass as
-- for K. A normalized-law reading instead requires IsDist (sigma g).
-- The non-caught marginal bound below is imposed at every full history
-- for every size-B schedule; sigma itself has no schedule argument.
def Back_sc07_fixed_budget : Prop :=
  ∀ (N B S q : ℕ) (r : ℝ) (Y : Type) [Fintype Y]
      (sigma : List (AOut Unit) → Bool → ℝ)
      (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ),
    B ≤ N →
    0 ≤ r → r ≤ 1 →
    (∀ g a, 0 ≤ sigma g a) →
    (∀ g, (∑ a, sigma g a) ≤ 1) →
    (∀ sched ∈ ControlStack.AuditBudget.randomSchedules N B,
      ∀ h z, 0 ≤ K sched h z) →
    (∀ sched ∈ ControlStack.AuditBudget.randomSchedules N B,
      ∀ h, (∑ y, ∑ o, K sched h (y, o)) ≤ 1) →
    (∀ sched ∈ ControlStack.AuditBudget.randomSchedules N B,
      ∀ h a,
        (∑ y, K sched h (y, (a, (), false))) ≤
          sigma (h.map Prod.snd) a *
            (if memN sched (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) →
    (∑ sched : Finset (Fin N), ControlStack.ReservedAudit.pU N B sched *
      val (K sched) (ControlStack.ReservedRecall.recallSucc (N := N) (ceilDiv S q)) N []) ≤
      ControlStack.ReservedRecall.hypMiss N B (ceilDiv S q) r

end ControlStack.SC07Exfil
