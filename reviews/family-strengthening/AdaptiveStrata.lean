import Mathlib.Tactic
import Mathlib.Basic.NNReal.Defs

/-!
Review-scoped F6 composition across adaptively selected finite histories.

Given a real probability law, the weights represent the distribution of the
history actually reached by the adversary. The per-history miss/false-alarm
caps must hold for EVERY reachable history (including history-dependent
strategies). The bounds then do not require independence between detectors or
between histories. This file does NOT prove that a runtime monitor satisfies
those conditional caps, that histories cover all observations, or that samples
satisfy the assumed distribution.
-/

namespace ControlStack.AdaptiveStrata

open Finset

variable {H : Type} [DecidableEq H]

/-- A single uniform conditional cap controls the mixture even if the
attacker adaptively influences which history is reached. This is a
law-of-total-probability *algebraic* implication, conditional on externally
supplied, normalized history probabilities and per-history bounds. -/
theorem weighted_history_miss_bound
    (histories : Finset H) (historyProb missProb : H → NNReal)
    (missCap : NNReal)
    (hCap : ∀ h ∈ histories, missProb h ≤ missCap)
    (hWeights : (∑ h ∈ histories, historyProb h) ≤ 1) :
    (∑ h ∈ histories, historyProb h * missProb h) ≤ missCap := by
  calc
    (∑ h ∈ histories, historyProb h * missProb h)
        ≤ ∑ h ∈ histories, historyProb h * missCap := by
          apply Finset.sum_le_sum
          intro h hh
          exact mul_le_mul_of_nonneg_left (hCap h hh) (by positivity)
    _ = (∑ h ∈ histories, historyProb h) * missCap := by
          rw [Finset.sum_mul]
    _ ≤ 1 * missCap :=
          mul_le_mul_of_nonneg_right hWeights (by positivity)
    _ = missCap := one_mul _

/-- The missed-attack and benign-false-alarm distributions can be
DIFFERENT. Separate finite conditional caps bound both mixture risks;
neither detector independence nor equality of the two history laws is
assumed. Both class-specific probability normalization hypotheses are
explicit rather than hidden in a definition. -/
theorem weighted_history_two_class_bounds
    (histories : Finset H)
    (attackHistoryProb benignHistoryProb : H → NNReal)
    (missProb falseAlarmProb : H → NNReal)
    (missCap falseAlarmCap : NNReal)
    (hMiss : ∀ h ∈ histories, missProb h ≤ missCap)
    (hFalse : ∀ h ∈ histories, falseAlarmProb h ≤ falseAlarmCap)
    (hAttackMass : (∑ h ∈ histories, attackHistoryProb h) ≤ 1)
    (hBenignMass : (∑ h ∈ histories, benignHistoryProb h) ≤ 1) :
    (∑ h ∈ histories, attackHistoryProb h * missProb h) ≤ missCap ∧
    (∑ h ∈ histories, benignHistoryProb h * falseAlarmProb h) ≤ falseAlarmCap := by
  constructor
  · exact weighted_history_miss_bound histories attackHistoryProb missProb
      missCap hMiss hAttackMass
  · exact weighted_history_miss_bound histories benignHistoryProb falseAlarmProb
      falseAlarmCap hFalse hBenignMass

#print axioms weighted_history_miss_bound
#print axioms weighted_history_two_class_bounds

end ControlStack.AdaptiveStrata
