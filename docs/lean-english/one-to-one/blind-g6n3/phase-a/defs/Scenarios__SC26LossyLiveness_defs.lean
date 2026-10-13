-- EXCERPT of ControlStack/Scenarios/SC26LossyLiveness.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC26LossyLiveness

open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26Liveness.Concrete



inductive LOp where
  | base (o : COp)
  | drop (j : ℕ)
  | dup (j : ℕ)
  | deliverAt (j : ℕ)
deriving DecidableEq, Repr

/-- the bank's processing: idempotent by key (deployed), or appending (witness (4) only) -/
def procWith (dedup : Bool) (bank : List (ℕ × Tx)) (key : ℕ) (tx : Tx) : List (ℕ × Tx) :=
  if dedup then bankApply bank key tx else bank ++ [(key, tx)]

def stepL (R : Roles) (cap : ℕ) (dedup : Bool) (s : CSt) : LOp → CSt
  | .base o => stepC R cap true s o
  | .drop j => { s with wire := s.wire.eraseIdx j }
  | .dup j =>
    match s.wire[j]? with
    | none => s
    | some m => { s with wire := s.wire ++ [m] }
  | .deliverAt j =>
    match s.wire[j]? with
    | none => s
    | some m => { s with bank := procWith dedup s.bank m.1 m.2 }

def runL (R : Roles) (cap : ℕ) (dedup : Bool) (s : CSt) (ops : List LOp) : CSt := ops.foldl (stepL R cap dedup) s

/-- untrusted operations never carry the gate credential; network operations are unrestricted -/
def legalL (R : Roles) : LOp → Prop
  | .base o => legalC R o
  | _ => True



def opsOfL (s : CSt) : LOp → List Op
  | .base o => opsOf s o
  | .deliverAt j =>
    match s.wire[j]? with
    | none => []
    | some m => [.arrive m.1]
  | _ => []

def absTraceL (R : Roles) (cap : ℕ) : CSt → List LOp → List Op
  | _, [] => []
  | s, o :: ops => opsOfL s o ++ absTraceL R cap (stepL R cap true s o) ops

/-- what survives loss: delivery rows (by id and payload), bank keys, halting. The wire does NOT persist. -/
structure LMono (s t : CSt) : Prop where
  rows : ∀ d ∈ s.delivery, ∃ d' ∈ t.delivery, d'.id = d.id ∧ d'.tx = d.tx
  bank : ∀ x ∈ s.bank.map Prod.fst, x ∈ t.bank.map Prod.fst
  halt : s.halted = true → t.halted = true

/-- a segment in which the network loses nothing -/
def DropFree (l : List LOp) : Prop := ∀ o ∈ l, ∀ j, o ≠ .drop j

/-- a retransmission round: arbitrary operations, the gate's retransmission, then network/adversary operations -/
def roundOps (r : List LOp × List LOp) : List LOp := r.1 ++ .base .recover :: r.2

/-- the round's retransmission is DELIVERED: the bank processes `k` before the network loses anything -/
def Delivers (k : ℕ) (r : List LOp × List LOp) : Prop :=
  ∃ nd rest, r.2 = nd ++ .base (.bankProcess k) :: rest ∧ DropFree nd

/-- the gate's setup for the witnesses: request, approval, reservation and logged intent for key 0 -/
def setupOps : List LOp := [.base (.request 1 wTx), .base (.approve 2 0 wTx), .base (.execute 1 0), .base (.deliver 0)]

/-- the adversary loses every retransmission -/
def dropRound : List LOp := [.base .recover, .drop 0, .base (.bankProcess 0)]

/-- the first transmission is lost; the gate crashes, recovers and retransmits; the network duplicates the
retransmission and delivers both copies -/
def lossDupTrace : List LOp :=
  [.base (.transmit 0), .drop 0, .base .crash, .base .recover, .dup 0, .deliverAt 0, .deliverAt 1]

end ControlStack.SC26LossyLiveness

