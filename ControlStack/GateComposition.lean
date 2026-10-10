import Std

/-!
Shared-state composition is NOT implied by proving separate gate invariants
under separate state assumptions. Here both proof obligations apply to the
*same* state and every step of the joint action alphabet. A confused-deputy
countermodel shows why independent gate checks are insufficient.

Source-level candidate pending kernel replay and a concrete runtime refinement.
-/
namespace ControlStack.GateComposition

def run {S A : Type} (step : S → A → S) (s : S) (actions : List A) : S :=
  actions.foldl step s

/-- Both invariants survive all shared-state actions if each joint transition
preserves both simultaneously. Quantifies over any finite action trace. -/
theorem shared_invariants {S A : Type} (P Q : S → Prop) (step : S → A → S)
    (s : S) (actions : List A)
    (hJoint : ∀ (x : S) (a : A), P x → Q x → P (step x a) ∧ Q (step x a))
    (h : P s ∧ Q s) :
    P (run step s actions) ∧ Q (run step s actions) := by
  induction actions generalizing s with
  | nil => simpa [run] using h
  | cons a rest ih =>
    change P (run step (step s a) rest) ∧ Q (run step (step s a) rest)
    exact ih (step s a) (hJoint s a h.1 h.2)

structure DeputyState where
  gateAApproved : Bool
  gateBApproved : Bool
  externalEffect : Bool

inductive DeputyOp where
  | directRequest
  | invokeTrustedDeputy

/-- Intentionally UNSAFE example: the deputy trusts A's credential to perform
an effect protected by B, without verifying B's independent authorization. -/
def unsafeDeputyStep (s : DeputyState) : DeputyOp → DeputyState
  | .directRequest => { s with externalEffect := s.externalEffect || s.gateBApproved }
  | .invokeTrustedDeputy =>
      { s with externalEffect := s.externalEffect || s.gateAApproved }

theorem confused_deputy_counterexample :
    (unsafeDeputyStep
      { gateAApproved := true, gateBApproved := false, externalEffect := false }
      .invokeTrustedDeputy).externalEffect = true := by
  rfl

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
#print axioms shared_invariants
#print axioms confused_deputy_counterexample

end ControlStack.GateComposition
