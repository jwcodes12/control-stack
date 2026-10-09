/-
F4 availability hardening: nonce issuance is bound to one intended session key.

The legacy AttestedKeyRelease.issue creates a global nonce. A second, genuinely
attested session can quote and spend it first. The existing F4 proof establishes
release safety but its uninterrupted honest_liveness trace does not rule out
this competing-session denial of service.

This module models a broker API with issueFor(sessionKey), requestFor(key,report):
  * a nonce can be issued only for a live session key;
  * requestFor demands the issued (nonce, key) pair AND all legacy full checks;
  * raw issue/request are explicitly unavailable to clients.
Other operations are interpreted using the original full-check machine.

This is a modeled protocol change, not a claim that the Python or any deployed
broker already implements session-bound nonce storage and authentication.
In particular caller authentication, concurrent atomicity and fairness are
not established by this finite-state model.
-/
import ControlStack.Families.F4.AttestedKeyRelease

namespace ControlStack.SessionBoundNonce

open ControlStack.AttestedKeyRelease

/-- A broker's original state plus its private nonce-to-session assignment table. -/
structure St where
  base : ControlStack.AttestedKeyRelease.St
  issuedTo : List (ℕ × ℕ)
deriving DecidableEq, Repr

/-- The untrusted client cannot invoke the old global issue or request directly. -/
inductive Op where
  | issueFor (session : ℕ)
  | requestFor (session : ℕ) (report : Report)
  | plain (old : ControlStack.AttestedKeyRelease.Op)
deriving DecidableEq, Repr

def init (allow : List ℕ) : St := ⟨ControlStack.AttestedKeyRelease.init allow, []⟩

/-- Fail closed on raw issue/request; otherwise add the session ownership check to
the old signature/freshness/allowlist/report-binding checks. -/
def step (admins : List ℕ) (expiry : ℕ) (s : St) : Op → St
  | .issueFor k =>
      if (codeOf s.base k).isSome then
        { base := ControlStack.AttestedKeyRelease.step admins expiry full s.base .issue
          issuedTo := s.issuedTo ++ [(s.base.nextNonce, k)] }
      else s
  | .requestFor k r =>
      if (r.nonce, k) ∈ s.issuedTo then
        { s with base := ControlStack.AttestedKeyRelease.step admins expiry full s.base (.request k r) }
      else s
  | .plain .issue => s
  | .plain (.request _ _) => s
  | .plain op => { s with base := ControlStack.AttestedKeyRelease.step admins expiry full s.base op }

def run (admins : List ℕ) (expiry : ℕ) (s : St) (ops : List Op) : St :=
  ops.foldl (step admins expiry) s

/-- A session cannot spend a nonce assigned only to another session. The
unchanged state includes both the original used-nonce list and release log. -/
example (admins : List ℕ) (expiry : ℕ) (s : St) (k : ℕ) (r : Report)
    (h : (r.nonce, k) ∉ s.issuedTo) : step admins expiry s (.requestFor k r) = s := by
  simp [step, h]

/-- Raw legacy nonce issuance does not bypass ownership. -/
example (admins : List ℕ) (expiry : ℕ) (s : St) :
    step admins expiry s (.plain .issue) = s := rfl

/-- Raw legacy key release does not bypass ownership. -/
example (admins : List ℕ) (expiry : ℕ) (s : St) (k : ℕ) (r : Report) :
    step admins expiry s (.plain (.request k r)) = s := rfl

/-- Original model: two honest allowlisted sessions quote globally issued nonce 0.
The second spends it first, so the intended first session cannot decrypt. -/
private def oldRace : List ControlStack.AttestedKeyRelease.Op :=
  [.spawn 1, .spawn 1, .issue, .quote 0 0, .quote 1 0,
   .request 1 ⟨1, 0, 1⟩, .request 0 ⟨1, 0, 0⟩,
   .decrypt 0, .decrypt 1]

example :
    (ControlStack.AttestedKeyRelease.run [0] 2 full
      (ControlStack.AttestedKeyRelease.init [1]) oldRace).decs = [(1, 1, 0)] := by
  decide

/-- Hardened model, same schedule: the rival's spend is refused; the intended
session completes. This witnesses the particular fixed interference mechanism,
not liveness against arbitrary network delay or adversarial interleavings. -/
private def fixedRace : List Op :=
  [.plain (.spawn 1), .plain (.spawn 1), .issueFor 0,
   .plain (.quote 0 0), .plain (.quote 1 0),
   .requestFor 1 ⟨1, 0, 1⟩, .requestFor 0 ⟨1, 0, 0⟩,
   .plain (.decrypt 0), .plain (.decrypt 1)]

example :
    (run [0] 2 (init [1]) fixedRace).base.decs = [(0, 1, 0)] ∧
    (run [0] 2 (init [1]) fixedRace).base.used = [0] := by
  decide

end ControlStack.SessionBoundNonce
