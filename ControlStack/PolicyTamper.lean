import ControlStack.EgressGate

/-!
SC-03 / SC-10: explicit policy-tampering variant. Not an OS integrity proof.
The legacy EgressGate fixes its policy as a parameter and makes tamperPolicy
a no-op; here attacker policy-write authority is an explicit boolean premise.
This file is source-only until a separate Lean kernel/axiom replay is recorded.
-/
namespace ControlStack.PolicyTamper

abbrev Policy := ControlStack.EgressGate.Policy

structure St where
  activePolicy : Policy
  requests : Nat

inductive Op where
  | request
  | attemptPolicyWrite (replacement : Policy)

def step (attackerCanWrite : Bool) (s : St) : Op → St
  | .request => { s with requests := s.requests + 1 }
  | .attemptPolicyWrite replacement =>
      if attackerCanWrite then { s with activePolicy := replacement } else s

def run (attackerCanWrite : Bool) (s : St) (ops : List Op) : St :=
  ops.foldl (step attackerCanWrite) s

/-- Conditional integrity: only if the attacker cannot modify the active
policy does a list of attacker operations preserve its exact identity. -/
theorem policy_preserved_if_protected (p : Policy) (s : St) (ops : List Op)
    (h : s.activePolicy = p) : (run false s ops).activePolicy = p := by
  induction ops generalizing s with
  | nil => simpa [run] using h
  | cons a rest ih =>
    change (run false (step false s a) rest).activePolicy = p
    apply ih
    cases a <;> simpa [step] using h

/-- Necessity witness: with policy-write authority, a single attacker action
replaces the active policy. This does not rely on a "tamper is no-op" axiom. -/
theorem tamper_possible_if_writable (s : St) (replacement : Policy) :
    (step true s (.attemptPolicyWrite replacement)).activePolicy = replacement := by
  rfl

#print axioms policy_preserved_if_protected
#print axioms tamper_possible_if_writable

end ControlStack.PolicyTamper
