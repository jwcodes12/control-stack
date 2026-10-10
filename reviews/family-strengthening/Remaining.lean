import Mathlib.Tactic
import Mathlib.Data.NNReal.Defs

/-!
Review-scoped, finite weighted adaptive-monitor boundary.

The caller supplies a nonnegative conditional sample mass for each history.
There is deliberately NO independence assumption between monitors, no
assertion of empirically measured recall and no assertion that the set of
histories captures every runtime observation or adaptive strategy.
-/
namespace ControlStack.MonitorHistory

open Finset

variable {H Ω : Type} [DecidableEq H] [DecidableEq Ω]

/-- A history-indexed miss mass. False alarms are excluded from the missed
ATTACK population; they must be counted separately in usefulness analysis. -/
def missMass (traces : H → Finset Ω) (attacks alarms : H → Finset Ω)
    (weight : H → Ω → NNReal) (h : H) : NNReal :=
  ∑ x ∈ traces h, if x ∈ attacks h ∧ x ∉ alarms h then weight h x else 0

/-- A history-indexed false alarm mass (ordinary outcomes flagged as attacks). -/
def falseAlarmMass (traces : H → Finset Ω) (attacks alarms : H → Finset Ω)
    (weight : H → Ω → NNReal) (h : H) : NNReal :=
  ∑ x ∈ traces h, if x ∉ attacks h ∧ x ∈ alarms h then weight h x else 0

/-- Sum of per-history measured/assumed miss caps. The crucial probabilistic
premise is explicit: for EVERY history in scope, missMass ≤ cap. Arbitrary
correlations of detectors are permitted; this says nothing about histories
not in scope, normalization or the source of the caps. -/
theorem adaptive_miss_mass_le_budgets
    (histories : Finset H) (traces : H → Finset Ω)
    (attacks alarms : H → Finset Ω) (weight : H → Ω → NNReal)
    (cap : H → NNReal)
    (hCap : ∀ h ∈ histories, missMass traces attacks alarms weight h ≤ cap h) :
    (∑ h ∈ histories, missMass traces attacks alarms weight h) ≤
      ∑ h ∈ histories, cap h := by
  exact Finset.sum_le_sum hCap

/-- A missed attack and a false alarm cannot be the same outcome at a fixed
history under the explicitly partitioned bad/benign predicates. -/
theorem miss_excludes_false_alarm (attacks alarms : Finset Ω) {x : Ω}
    (hmiss : x ∈ attacks ∧ x ∉ alarms)
    (hfp : x ∉ attacks ∧ x ∈ alarms) : False := by
  exact hfp.1 hmiss.1

#print axioms adaptive_miss_mass_le_budgets
#print axioms miss_excludes_false_alarm

end ControlStack.MonitorHistory

/-!
An explicit multi-agent abstract release machine. Unlike the generic F8
theorem, the global budget, absorbing HALT and monotonic admission count
are derived from the concrete transition definition for arbitrary agent-ID
interleavings. No claim is made that an OS process refines this transition.
-/
namespace ControlStack.JointAdmission

structure State where
  cap : Nat
  spent : Nat
  halted : Bool
  admitted : Nat
  deriving DecidableEq, Repr

inductive Action where
  | request (agent : Nat) (cost : Nat)
  | halt
  | tick
  deriving DecidableEq, Repr

def step (s : State) (a : Action) : State :=
  match a with
  | .halt => { s with halted := true }
  | .tick => s
  | .request _ cost =>
      if s.halted = true ∨ cost = 0 ∨ s.spent + cost > s.cap then s
      else { s with spent := s.spent + cost, admitted := s.admitted + 1 }

def run (s : State) (actions : List Action) : State :=
  actions.foldl step s

theorem budget_step (s : State) (a : Action)
    (hs : s.spent ≤ s.cap) : (step s a).spent ≤ (step s a).cap := by
  cases a with
  | halt => simpa [step] using hs
  | tick => simpa [step] using hs
  | request agent cost =>
      by_cases h : s.halted = true ∨ cost = 0 ∨ s.spent + cost > s.cap
      · simpa [step, h] using hs
      · have hcap : s.spent + cost ≤ s.cap := by omega
        simpa [step, h] using hcap

theorem budget_run (s : State) (actions : List Action)
    (hs : s.spent ≤ s.cap) : (run s actions).spent ≤ (run s actions).cap := by
  induction actions generalizing s with
  | nil => simpa [run] using hs
  | cons action rest ih =>
      change (run (step s action) rest).spent ≤
        (run (step s action) rest).cap
      exact ih (step s action) (budget_step s action hs)

theorem halted_step (s : State) (a : Action)
    (h : s.halted = true) : (step s a).halted = true := by
  cases a with
  | halt => simp [step]
  | tick => simpa [step] using h
  | request agent cost => simp [step, h]

theorem halted_no_new_admission (s : State) (a : Action)
    (h : s.halted = true) : (step s a).admitted = s.admitted := by
  cases a with
  | halt => simp [step]
  | tick => simp [step]
  | request agent cost => simp [step, h]

theorem halted_run (s : State) (actions : List Action)
    (h : s.halted = true) : (run s actions).halted = true := by
  induction actions generalizing s with
  | nil => simpa [run] using h
  | cons action rest ih =>
      change (run (step s action) rest).halted = true
      exact ih (step s action) (halted_step s action h)

theorem no_admissions_after_halt (s : State) (actions : List Action)
    (h : s.halted = true) : (run s actions).admitted = s.admitted := by
  induction actions generalizing s with
  | nil => simpa [run] using rfl
  | cons action rest ih =>
      change (run (step s action) rest).admitted = s.admitted
      calc
        (run (step s action) rest).admitted =
            (step s action).admitted := ih (step s action) (halted_step s action h)
        _ = s.admitted := halted_no_new_admission s action h

/-- Witness that our admission machine does useful work; the invariants do
not follow only because it is frozen or refuses everything. -/
theorem accepts_one_valid_request :
    (step ⟨2, 0, false, 0⟩ (.request 17 1)).admitted = 1 := by
  decide

#print axioms budget_step
#print axioms budget_run
#print axioms halted_run
#print axioms no_admissions_after_halt
#print axioms accepts_one_valid_request

end ControlStack.JointAdmission
