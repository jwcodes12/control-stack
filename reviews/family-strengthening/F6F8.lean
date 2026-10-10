import Mathlib.Tactic

/-!
F6 non-independent ensemble sanity boundary.

Two fallible detectors on the SAME finite sample population have a joint
escape set equal to the intersection of their individual miss sets. No
independence or conditional-recall claim is smuggled in. Its size is at most
the size of either miss set, but need not obey a product-rate bound.
False positives affect usefulness separately, not the formal miss inclusion.
-/
namespace ControlStack.CorrelatedMonitor

open Finset

variable {α : Type} [DecidableEq α]

/-- Adding a detector never INCREASES missed cases on the same population.
This theorem does not give multiplicative improvement without a coupling law. -/
theorem joint_misses_le_each (missA missB : Finset α) :
    (missA ∩ missB).card ≤ min missA.card missB.card := by
  apply le_min
  · exact card_le_card inter_subset_left
  · exact card_le_card inter_subset_right

/-- Fully correlated misses refute the naive independence/product-rate
assumption even with individual recall exactly 1/2. Population 4, both
detectors miss the same two cases: joint miss count is 2, not 1. -/
theorem correlated_miss_counterexample :
    let population : Finset ℕ := {0, 1, 2, 3}
    let missA : Finset ℕ := {0, 1}
    let missB : Finset ℕ := {0, 1}
    missA.card * 2 = population.card ∧
    missB.card * 2 = population.card ∧
    (missA ∩ missB).card * population.card > missA.card * missB.card := by
  decide

/-- A false-positive alarm cannot be treated as a detection of a bad
action: if false-positive and true-attack sets are disjoint, such an alarm
belongs to the complement of the true attack set. -/
theorem false_alarm_is_not_attack (attacks falseAlarms : Finset α)
    (h : Disjoint attacks falseAlarms) {x : α} (hf : x ∈ falseAlarms) :
    x ∉ attacks := by
  intro ha
  exact (disjoint_left.mp h) ha hf

#print axioms joint_misses_le_each
#print axioms correlated_miss_counterexample
#print axioms false_alarm_is_not_attack

end ControlStack.CorrelatedMonitor

namespace ControlStack.GateComposition

/-- A finite family of component invariants is preserved under arbitrary
interleaving only when EVERY joint step preserves ALL of them simultaneously.
This stronger quantification does not establish complete external mediation. -/
theorem shared_family_invariants {S A ι : Type} (I : ι → S → Prop)
    (step : S → A → S) (s : S) (actions : List A)
    (hJoint : ∀ (x : S) (a : A), (∀ i, I i x) → ∀ i, I i (step x a))
    (hInit : ∀ i, I i s) :
    ∀ i, I i (run step s actions) := by
  induction actions generalizing s with
  | nil => simpa [run] using hInit
  | cons a rest ih =>
      change ∀ i, I i (run step (step s a) rest)
      exact ih (step s a) (hJoint s a hInit)

#print axioms shared_family_invariants

end ControlStack.GateComposition
