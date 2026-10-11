import Mathlib.Tactic

/-!
F8 REVIEW-SCOPED two-approval, two-agent, one-delegate joint runtime model.

This is a nontrivial GLOBAL shared-budget model for both independent and
delegated releases, immutable grant ownership, revocation, HALT and
publication. It deliberately omits SQLite, broker UID authentication,
expiry, OS kernels, crash/power loss and arbitrary side effects.
-/
namespace ControlStack.DelegatedFleet

structure State where
  cap : Nat
  spent : Nat
  halted : Bool
  grant : Bool
  revoked : Bool
  usedA : Bool
  usedB : Bool
  publishedA : Bool
  publishedB : Bool
  ownerA : Nat
  delegateA : Nat
  ownerB : Nat
  deriving DecidableEq

inductive Action where
  | grant (actor : Nat)
  | revoke (actor : Nat)
  | releaseA (actor : Nat)
  | releaseB (actor : Nat)
  | publishA
  | publishB
  | halt
  deriving DecidableEq

/-- Trust assumptions: a trusted gate serializes these actions; ownerA,
delegateA and ownerB are authentic, preapproved OS principals. The fixed
single-unit charge is the broker's reference release cost, not real CPU/I/O.
Permission/expiry checks not represented here can only deny more actions. -/
def step (s : State) (a : Action) : State :=
  match a with
  | .grant actor =>
      if s.halted = true ∨ s.grant = true ∨ s.revoked = true ∨
         s.usedA = true ∨ actor ≠ s.ownerA ∨ s.delegateA = s.ownerA
      then s else { s with grant := true }
  | .revoke actor =>
      if s.halted = true ∨ s.grant = false ∨ actor ≠ s.ownerA
      then s else { s with revoked := true }
  | .releaseA actor =>
      if s.halted = true ∨ s.usedA = true ∨ s.revoked = true ∨
         s.spent + 1 > s.cap ∨
         (s.grant = true ∧ actor ≠ s.delegateA) ∨
         (s.grant = false ∧ actor ≠ s.ownerA)
      then s else { s with spent := s.spent + 1, usedA := true }
  | .releaseB actor =>
      if s.halted = true ∨ s.usedB = true ∨
         s.spent + 1 > s.cap ∨ actor ≠ s.ownerB
      then s else { s with spent := s.spent + 1, usedB := true }
  | .publishA =>
      if s.halted = true ∨ s.revoked = true ∨ s.usedA = false
      then s else { s with publishedA := true }
  | .publishB =>
      if s.halted = true ∨ s.usedB = false
      then s else { s with publishedB := true }
  | .halt => { s with halted := true }

def run (s : State) (actions : List Action) : State :=
  actions.foldl step s

/-- Both independent and delegated agents are serialized onto one cap. -/
theorem global_budget_step (s : State) (a : Action)
    (h : s.spent ≤ s.cap) : (step s a).spent ≤ (step s a).cap := by
  cases a with
  | grant actor =>
      by_cases denied : s.halted = true ∨ s.grant = true ∨
          s.revoked = true ∨ s.usedA = true ∨ actor ≠ s.ownerA ∨
          s.delegateA = s.ownerA
      · simpa [step, denied] using h
      · simpa [step, denied] using h
  | revoke actor =>
      by_cases denied : s.halted = true ∨ s.grant = false ∨
          actor ≠ s.ownerA
      · simpa [step, denied] using h
      · simpa [step, denied] using h
  | releaseA actor =>
      by_cases denied : s.halted = true ∨ s.usedA = true ∨
          s.revoked = true ∨ s.spent + 1 > s.cap ∨
          (s.grant = true ∧ actor ≠ s.delegateA) ∨
          (s.grant = false ∧ actor ≠ s.ownerA)
      · simpa only [step, if_pos denied] using h
      · have within_cap : s.spent + 1 ≤ s.cap := by omega
        simpa only [step, if_neg denied] using within_cap
  | releaseB actor =>
      by_cases denied : s.halted = true ∨ s.usedB = true ∨
          s.spent + 1 > s.cap ∨ actor ≠ s.ownerB
      · simpa only [step, if_pos denied] using h
      · have within_cap : s.spent + 1 ≤ s.cap := by omega
        simpa only [step, if_neg denied] using within_cap
  | publishA =>
      by_cases denied : s.halted = true ∨ s.revoked = true ∨
          s.usedA = false
      · simpa [step, denied] using h
      · simpa [step, denied] using h
  | publishB =>
      by_cases denied : s.halted = true ∨ s.usedB = false
      · simpa [step, denied] using h
      · simpa [step, denied] using h
  | halt => simpa [step] using h

theorem global_budget_run (s : State) (actions : List Action)
    (h : s.spent ≤ s.cap) :
    (run s actions).spent ≤ (run s actions).cap := by
  induction actions generalizing s with
  | nil => simpa [run] using h
  | cons a rest ih =>
      change (run (step s a) rest).spent ≤ (run (step s a) rest).cap
      exact ih (step s a) (global_budget_step s a h)

/-- A revoked delegated authorization cannot become a fresh admission. -/
theorem revoked_blocks_A (s : State) (actor : Nat)
    (h : s.revoked = true) : step s (.releaseA actor) = s := by
  simp [step, h]

/-- With an active grant, the original owner may not retake the nonce. -/
theorem original_owner_denied (s : State)
    (hGrant : s.grant = true)
    (hDistinct : s.ownerA ≠ s.delegateA) :
    step s (.releaseA s.ownerA) = s := by
  simp [step, hGrant, hDistinct]

/-- A release not yet admitted cannot cause local publication. -/
theorem no_A_publication_without_admission (s : State)
    (h : s.usedA = false) :
    (step s .publishA).publishedA = s.publishedA := by
  simp [step, h]

theorem no_B_publication_without_admission (s : State)
    (h : s.usedB = false) :
    (step s .publishB).publishedB = s.publishedB := by
  simp [step, h]

theorem halted_preserves_publication (s : State) (a : Action)
    (h : s.halted = true) :
    (step s a).publishedA = s.publishedA ∧
    (step s a).publishedB = s.publishedB := by
  cases a <;> simp [step, h]

theorem halted_absorbing (s : State) (a : Action)
    (h : s.halted = true) : (step s a).halted = true := by
  cases a <;> simp [step, h]

/-- Non-vacuous two-agent witness: the delegate and a different direct owner
both spend one shared budget unit when cap is 2. -/
theorem two_agent_positive :
    let initial : State :=
      ⟨2, 0, false, false, false, false, false,
       false, false, 1, 2, 3⟩
    let outcome := run initial [.grant 1, .releaseA 2, .releaseB 3]
    outcome.spent = 2 ∧ outcome.usedA = true ∧ outcome.usedB = true := by
  decide

/-- A cap of one allows at most one of the two independent releases. -/
theorem one_budget_slot :
    let initial : State :=
      ⟨1, 0, false, false, false, false, false,
       false, false, 1, 2, 3⟩
    let outcome := run initial [.grant 1, .releaseA 2, .releaseB 3]
    outcome.spent = 1 ∧ outcome.usedA = true ∧ outcome.usedB = false := by
  decide

#print axioms global_budget_step
#print axioms global_budget_run
#print axioms revoked_blocks_A
#print axioms original_owner_denied
#print axioms no_A_publication_without_admission
#print axioms no_B_publication_without_admission
#print axioms halted_preserves_publication
#print axioms halted_absorbing
#print axioms two_agent_positive
#print axioms one_budget_slot

end ControlStack.DelegatedFleet
