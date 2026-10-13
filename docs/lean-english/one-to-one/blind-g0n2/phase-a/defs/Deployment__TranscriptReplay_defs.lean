-- EXCERPT of ControlStack/Deployment/TranscriptReplay.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.
namespace ControlStack.Deployment.TranscriptReplay
open ControlStack

macro "ok" : tactic => `(tactic| first | rfl | exact Or.inl rfl | exact Or.inr rfl | decide)

def R : TrustedBroker.Roles :=
  { agent := fun u => u = 23701 ∨ u = 23702, reviewer := fun u => u = 23703, approver := fun u => u = 23704,
    admin := fun u => u = 23700, separated := by intro u h; rcases h with rfl | rfl <;> decide }

def s0 : TrustedBroker.State := TrustedBroker.initial 2

/-- The recorded `releases.created` of the archived database (database.sqlite, same run). Every issue/approve request in the transcript was
made no later than the first release, and every lease and approval expiry in it is strictly greater than this value. -/
def now : Nat := 1791658272
def s1 : TrustedBroker.State := { s0 with artifacts := TrustedBroker.put s0.artifacts 1 true, intact := TrustedBroker.put s0.intact 1 true }
def s2 : TrustedBroker.State := { s1 with reviews := TrustedBroker.put s1.reviews 1 (some 23703) }
def l1 : TrustedBroker.Lease := ⟨23701, 1, 0, 1791660071, false⟩
def s3 : TrustedBroker.State := { s2 with leases := TrustedBroker.put s2.leases 1 (some l1) }
def a1 : TrustedBroker.Approval := ⟨1, 1, 23701, 1, 23704, 1791660071, false⟩
def s4 : TrustedBroker.State := { s3 with approvals := TrustedBroker.put s3.approvals 1 (some a1) }
def s5 : TrustedBroker.State := { s4 with artifacts := TrustedBroker.put s4.artifacts 1 true, intact := TrustedBroker.put s4.intact 1 true }
def l2 : TrustedBroker.Lease := ⟨23702, 1, 0, 1791660071, false⟩
def s6 : TrustedBroker.State := { s5 with leases := TrustedBroker.put s5.leases 2 (some l2) }
def a2 : TrustedBroker.Approval := ⟨1, 1, 23702, 2, 23704, 1791660071, false⟩
def s7 : TrustedBroker.State := { s6 with approvals := TrustedBroker.put s6.approvals 2 (some a2) }
def q7 : TrustedBroker.Request := ⟨23701, 1, 1, 1, 1, 1⟩
def s8 : TrustedBroker.State := TrustedBroker.committed s7 q7 a1 l1
def q8 : TrustedBroker.Request := ⟨23701, 1, 1, 1, 1, 1⟩
def s9 : TrustedBroker.State := s8
def q9 : TrustedBroker.Request := ⟨23702, 2, 1, 1, 2, 1⟩
def s10 : TrustedBroker.State := TrustedBroker.committed s9 q9 a2 l2
def interpret : Nat → TrustedBroker.State
  | 0 => s0
  | 1 => s1
  | 2 => s2
  | 3 => s3
  | 4 => s4
  | 5 => s5
  | 6 => s6
  | 7 => s7
  | 8 => s8
  | 9 => s9
  | 10 => s10
  | _ => s0

def replayStep (s op : Nat) : Nat :=
  if s = 0 ∧ op = 0 then 1 else
  if s = 1 ∧ op = 1 then 2 else
  if s = 2 ∧ op = 2 then 3 else
  if s = 3 ∧ op = 3 then 4 else
  if s = 4 ∧ op = 4 then 5 else
  if s = 5 ∧ op = 5 then 6 else
  if s = 6 ∧ op = 6 then 7 else
  if s = 7 ∧ op = 7 then 8 else
  if s = 8 ∧ op = 8 then 9 else
  if s = 9 ∧ op = 9 then 10 else
  s

def table : IndexedBrokerTable R := ⟨interpret, replayStep, table_checked⟩

def receipts : List (CheckedTrace.Receipt Nat Nat) := [⟨0, 0, 1⟩, ⟨1, 1, 2⟩, ⟨2, 2, 3⟩, ⟨3, 3, 4⟩, ⟨4, 4, 5⟩, ⟨5, 5, 6⟩, ⟨6, 6, 7⟩, ⟨7, 7, 8⟩, ⟨8, 8, 9⟩, ⟨9, 9, 10⟩]

/-- Dropping a state-changing receipt from the middle breaks the chain: the checker rejects it. -/
def withoutMiddleRelease : List (CheckedTrace.Receipt Nat Nat) := receipts.eraseIdx 7
/-- Dropping the recorded tail leaves a valid shorter trace: truncation is accepted. Completeness is not checked. -/
def withoutLastRelease : List (CheckedTrace.Receipt Nat Nat) := receipts.take 9
/-- Dropping the denied replay's receipt breaks the chain of recorded state ids, so this checker rejects it. A producer that
renumbered a shorter log consistently would be accepted: the checker sees only the receipts it is given. -/
def withoutDenial : List (CheckedTrace.Receipt Nat Nat) := receipts.eraseIdx 8
end ControlStack.Deployment.TranscriptReplay
