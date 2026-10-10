import Mathlib.Tactic

/-!
A ONE-NONCE, single-hop delegated-release transition model, not a proof of
Python/SQLite/OS correspondence. Assumes an already-reviewed active exact
approval and lease, positive fixed cost 1, authentic actor IDs and serialized
trusted operations. No external effect is modeled. In particular, expiration,
identity authentication, clock validity and grant provenance remain outside.
-/
namespace ControlStack.DelegatedAdmission

structure State where
  cap : Nat
  spent : Nat
  halted : Bool
  owner : Nat
  admin : Nat
  grant : Option Nat
  revoked : Bool
  used : Bool
  deriving DecidableEq, Repr

inductive Action where
  | grant (actor delegate : Nat)
  | revoke (actor : Nat)
  | use (actor : Nat)
  | halt (actor : Nat)
  deriving DecidableEq, Repr

def step (s : State) (a : Action) : State :=
  match a with
  | .grant actor delegate =>
      if s.halted = true ∨ s.used = true ∨ s.revoked = true ∨
         actor ≠ s.owner ∨ delegate = s.owner ∨ s.grant ≠ none
      then s else { s with grant := some delegate }
  | .revoke actor =>
      if s.halted = true ∨ (actor ≠ s.owner ∧ actor ≠ s.admin) ∨
         s.grant = none
      then s else { s with revoked := true }
  | .use actor =>
      if s.halted = true ∨ s.used = true ∨ s.revoked = true ∨
         s.spent + 1 > s.cap ∨
         (if s.grant = none then actor ≠ s.owner
          else s.grant ≠ some actor)
      then s else { s with spent := s.spent + 1, used := true }
  | .halt actor =>
      if actor = s.admin then { s with halted := true } else s

def run (s : State) (actions : List Action) : State :=
  actions.foldl step s

/-- The one-hop grant is a restriction: without a grant only its owner can
spend the approved nonce; numeric UID equality is an EXTERNAL assumption. -/
theorem stranger_without_grant_denied (s : State) (actor : Nat)
    (hNone : s.grant = none) (hOther : actor ≠ s.owner) :
    step s (.use actor) = s := by
  simp [step, hNone, hOther]

/-- Once delegated, the original owner cannot take the nonce back to spend. -/
theorem original_owner_denied_after_grant (s : State) (delegate : Nat)
    (hGrant : s.grant = some delegate) (hOther : delegate ≠ s.owner) :
    step s (.use s.owner) = s := by
  simp [step, hGrant, hOther]

/-- Revocation cannot be bypassed by a peer request in this model. -/
theorem revoked_blocks_use (s : State) (actor : Nat)
    (h : s.revoked = true) : step s (.use actor) = s := by
  simp [step, h]

/-- The HALT state prevents any later consumption. -/
theorem halted_blocks_use (s : State) (actor : Nat)
    (h : s.halted = true) : step s (.use actor) = s := by
  simp [step, h]

/-- One joint cap applies to owners and delegates in the modeled transition.
No independent per-agent counters or borrowed budgets exist here. -/
theorem budget_step (s : State) (a : Action) (h : s.spent ≤ s.cap) :
    (step s a).spent ≤ (step s a).cap := by
  cases a <;> simp only [step] <;> split <;> simp_all <;> omega

theorem budget_run (s : State) (actions : List Action)
    (h : s.spent ≤ s.cap) :
    (run s actions).spent ≤ (run s actions).cap := by
  induction actions generalizing s with
  | nil => simpa [run] using h
  | cons a rest ih =>
      change (run (step s a) rest).spent ≤ (run (step s a) rest).cap
      exact ih (step s a) (budget_step s a h)

/-- Positive witness: a real delegation tag may admit a release; the model
does not prove the runtime verified the tag against an actual peer UID. -/
theorem delegated_positive_witness :
    let init : State := ⟨1, 0, false, 1, 9, none, false, false⟩
    (run init [.grant 1 2, .use 2]).spent = 1 ∧
    (run init [.grant 1 2, .use 2]).used = true := by
  decide

#print axioms stranger_without_grant_denied
#print axioms original_owner_denied_after_grant
#print axioms revoked_blocks_use
#print axioms halted_blocks_use
#print axioms budget_step
#print axioms budget_run
#print axioms delegated_positive_witness

end ControlStack.DelegatedAdmission
