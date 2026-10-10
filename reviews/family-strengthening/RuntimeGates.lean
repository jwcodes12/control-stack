import Mathlib.Tactic
import ControlStack.GateComposition

/-! Candidate machine-checkable F6 conditional-recall / false-positive bound
and F8 concrete shared-budget interleaving. None measures a live monitor or
proves that actual agent effects are exclusively mediated. -/

namespace ControlStack.ReviewF6

open Finset

/-- Adaptive-history mixtures require an assumption for every reachable
history. The weights can encode adversary-dependent feedback; detector
independence is not assumed. False alarms are bounded SEPARATELY. -/
theorem weighted_conditional_monitor_bound
    {H : Type} [DecidableEq H] (histories : Finset H) (weight miss falseAlarm : H → ℚ)
    (eps delta : ℚ)
    (hWeight : ∀ h ∈ histories, 0 ≤ weight h)
    (hNorm : (∑ h ∈ histories, weight h) = 1)
    (hMiss : ∀ h ∈ histories, miss h ≤ eps)
    (hFP : ∀ h ∈ histories, falseAlarm h ≤ delta) :
    (∑ h ∈ histories, weight h * miss h) ≤ eps ∧
    (∑ h ∈ histories, weight h * falseAlarm h) ≤ delta := by
  constructor
  · calc
      (∑ h ∈ histories, weight h * miss h) ≤
          (∑ h ∈ histories, weight h * eps) := by
            apply Finset.sum_le_sum
            intro h hh
            exact mul_le_mul_of_nonneg_left (hMiss h hh) (hWeight h hh)
      _ = eps := by rw [Finset.sum_mul, hNorm, one_mul]
  · calc
      (∑ h ∈ histories, weight h * falseAlarm h) ≤
          (∑ h ∈ histories, weight h * delta) := by
            apply Finset.sum_le_sum
            intro h hh
            exact mul_le_mul_of_nonneg_left (hFP h hh) (hWeight h hh)
      _ = delta := by rw [Finset.sum_mul, hNorm, one_mul]

#print axioms weighted_conditional_monitor_bound
end ControlStack.ReviewF6

namespace ControlStack.ReviewF8

structure BudgetState where
  spent : Nat
  halted : Bool
deriving DecidableEq, Repr

inductive BudgetOp where
  | halt
  | release (cost : Nat)
deriving DecidableEq, Repr

/-- Joint transition shared by all actors, rather than separately checked
actor-local budgets. It deliberately models only an abstract admission count. -/
def step (cap : Nat) (s : BudgetState) : BudgetOp → BudgetState
  | .halt => { s with halted := true }
  | .release cost =>
      if s.halted = false ∧ s.spent + cost ≤ cap
      then { s with spent := s.spent + cost }
      else s

theorem step_within_cap (cap : Nat) (s : BudgetState) (a : BudgetOp)
    (h : s.spent ≤ cap) : (step cap s a).spent ≤ cap := by
  cases a with
  | halt => simpa [step] using h
  | release cost =>
    unfold step
    split_ifs with hc
    · exact hc.2
    · exact h

theorem all_actor_interleavings_within_cap
    (cap : Nat) (s : BudgetState) (actions : List BudgetOp)
    (h : s.spent ≤ cap) :
    ((ControlStack.GateComposition.run (step cap) s actions).spent ≤ cap) := by
  induction actions generalizing s with
  | nil => simpa [ControlStack.GateComposition.run] using h
  | cons a rest ih =>
    change (ControlStack.GateComposition.run (step cap)
      (step cap s a) rest).spent ≤ cap
    exact ih (step cap s a) (step_within_cap cap s a h)

theorem sticky_halt (cap : Nat) (s : BudgetState) (a : BudgetOp)
    (h : s.halted = true) : (step cap s a).halted = true := by
  cases a with
  | halt => rfl
  | release cost => simp [step, h]

#print axioms step_within_cap
#print axioms all_actor_interleavings_within_cap
#print axioms sticky_halt
end ControlStack.ReviewF8
