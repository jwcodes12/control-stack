/-
SC-05: an agent coordinates a malicious action with a one-bit signal despite a 16-bit cap.

This scenario is a NEGATIVE test for broad "no collusion" claims, so the file states what can and cannot be claimed:
- `cap_does_not_prevent` (no-go, from `CovertNoGo.one_bit_coordinates`): under a 16-bit output cap, any two
  sender-realisable outputs the receiver can tell apart let colluders agree on a binary action with certainty. A
  cardinality cap never implies "no coordination"; it only bounds how many distinct messages get through
  (`Covert.covert_bound`: success ≤ |V|/|M|).
- `zero_dependence_is_blind` (positive, the first alternative the threat model names): if the mediated output's
  distribution does not depend on the secret at all (certified zero secret-dependence), the receiver's success equals
  the blind guess 1/|M|, whatever the shared seed and decoder.
- `forbidden_never_executes` (positive, the second alternative): a gate that prohibits the specific action (or
  recipient) is safe whatever signals pass between agents, because the signal can only choose among operations the gate
  still checks. `forbidden_executes_without_gate` is the witness that without it one bit suffices.

Adversary classes: `cap_does_not_prevent` and `zero_dependence_is_blind` quantify over SHARED_SEED encoders/decoders
(ADVERSARY-CLASSES.md); `forbidden_never_executes` is TRACE_ARBITRARY.

What remains semantic: deciding WHICH actions/recipients are "the malicious action" (the forbidden set), and whether an
output really has zero secret-dependence in a deployment (that is an observation-completeness premise, see SC-01/F2).
No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate
import ControlStack.CovertNoGo

namespace ControlStack.SC05

open ControlStack.Gate ControlStack.Covert ControlStack.CovertNoGo Finset

/-- **A 16-bit cap does not prevent one-bit coordination.** Over 2^16 possible outputs, two distinguishable ones let a
sender and receiver agree on a binary action with probability 1. -/
theorem cap_does_not_prevent :
    ∃ (enc : Bool → Fin 65536 → ℝ) (dec : Fin 65536 → Bool → ℝ),
      (∀ m, IsDist (enc m)) ∧ (∀ v, IsDist (dec v)) ∧ successView id enc dec = 1 :=
  one_bit_coordinates id 0 1 (by decide)

/-- **Zero secret-dependence is blind.** If the output distribution does not depend on the secret, the receiver's
success over a uniform secret is exactly 1/|M|, for every shared-seed distribution and decoder. -/
theorem zero_dependence_is_blind {Ω M V : Type} [Fintype Ω] [Fintype M] [Fintype V]
    (ρ : Ω → ℝ) (e : Ω → V → ℝ) (dec : Ω → V → M → ℝ)
    (hρ : IsDist ρ) (he : ∀ ω, IsDist (e ω)) (hdec : ∀ ω v, IsDist (dec ω v)) :
    successProb ρ (fun ω _ => e ω) dec = (Fintype.card M : ℝ)⁻¹ := by
  unfold successProb
  have h1 : ∀ ω, ∑ m, ∑ v, e ω v * dec ω v m = 1 := by
    intro ω
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (hdec ω _).2, mul_one]
    exact (he ω).2
  simp_rw [h1, mul_one]
  rw [← Finset.sum_mul, hρ.2, one_mul]

/-! ## Prohibiting the action itself -/

/-- executed actions; `act a` asks for action `a` (whatever signal led to the request) -/
inductive Op where
  | act (a : ℕ)
deriving DecidableEq, Repr

def step (forbidden : List ℕ) (gate : Bool) (s : List ℕ) : Op → List ℕ
  | .act a => if gate ∧ a ∈ forbidden then s else s ++ [a]

def sys (forbidden : List ℕ) : System (List ℕ) Op ℕ where
  step := step forbidden true
  effects := id

def spec (forbidden : List ℕ) : Spec (sys forbidden) where
  Inv := fun s => ∀ a ∈ s, a ∉ forbidden
  ok := fun _ a => a ∉ forbidden
  step_inv := by
    intro s o h
    cases o with
    | act a =>
      simp only [sys, step, true_and]
      split_ifs with ha
      · exact h
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact h x hx
        · simp at hx; subst hx; exact ha
  log_prefix := by
    intro s o
    cases o with
    | act a => simp only [sys, step, true_and]; split_ifs <;> simp
  inv_ok := fun _ h a ha => h a ha

/-- **The prohibited action never executes**, whatever the colluders signal (adversary: TRACE_ARBITRARY; the signal
only selects which operations are requested). -/
theorem forbidden_never_executes (forbidden : List ℕ) (ops : List Op) :
    ∀ a ∈ (sys forbidden).run [] ops, a ∉ forbidden :=
  ((spec forbidden).trace_safe [] ops (fun a ha => by simp at ha)).2.2

/-- without the gate, the bit the receiver decoded selects the forbidden action and it runs -/
theorem forbidden_executes_without_gate :
    (([Op.act 7].foldl (step [7] false) []) = [7]) ∧ (([Op.act 7].foldl (step [7] true) []) = []) := by
  decide

end ControlStack.SC05

#print axioms ControlStack.SC05.cap_does_not_prevent
#print axioms ControlStack.SC05.zero_dependence_is_blind
#print axioms ControlStack.SC05.spec
#print axioms ControlStack.SC05.forbidden_never_executes
#print axioms ControlStack.SC05.forbidden_executes_without_gate
