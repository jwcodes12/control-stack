-- EXCERPT of ControlStack/Scenarios/SC26Refinement.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC26Refinement

open ControlStack.SC26



/-- a delivery intent row (txgate's `delivery` table) -/
structure DRow where
  id : ℕ
  tx : Tx
  acked : Bool
deriving DecidableEq, Repr

structure CSt where
  next : ℕ
  reqs : List Req
  approvals : List (ℕ × ℕ × Tx)
  reserved : List ℕ
  spent : ℕ
  halted : Bool
  delivery : List DRow
  /-- volatile: the send in progress (delivery row index) -/
  inflight : Option ℕ
  /-- the network: every message physically transmitted -/
  wire : List (ℕ × Tx)
  /-- the bank's durable ledger -/
  bank : List (ℕ × Tx)
deriving DecidableEq, Repr

inductive COp where
  | request (caller : ℕ) (tx : Tx)
  | approve (caller : ℕ) (id : ℕ) (tx : Tx)
  | execute (caller : ℕ) (id : ℕ)
  | deliver (id : ℕ)
  | transmit (i : ℕ)
  | bankProcess (key : ℕ)
  | ack (i : ℕ)
  | crash
  | recover
  | halt (caller : ℕ)
  | bankCall (caller : ℕ) (key : ℕ) (tx : Tx)
deriving DecidableEq, Repr

def cinit : CSt := ⟨0, [], [], [], 0, false, [], none, [], []⟩

def creqOf (s : CSt) (id : ℕ) : Option Req := s.reqs.find? (fun r => r.id = id)

/-- the bank's processing of a transfer: idempotent by key (duplicate and conflict both leave the ledger unchanged) -/
def bankApply (bank : List (ℕ × Tx)) (key : ℕ) (tx : Tx) : List (ℕ × Tx) :=
  if key ∈ bank.map Prod.fst then bank else bank ++ [(key, tx)]

/-- acknowledge row i (txgate's `UPDATE delivery SET acked=1`), clearing the in-progress send -/
def ackSet (s : CSt) (i : ℕ) (d : DRow) : CSt :=
  { s with delivery := s.delivery.set i { d with acked := true }, inflight := none }

/-- the unacknowledged intents as messages -/
def unacked (s : CSt) : List (ℕ × Tx) := (s.delivery.filter (fun d => !d.acked)).map (fun d => (d.id, d.tx))

def stepC (R : Roles) (cap : ℕ) (recoverChecksHalt : Bool) (s : CSt) : COp → CSt
  | .request c tx =>
    if s.halted then s
    else if c ∈ R.agents then { s with reqs := s.reqs ++ [⟨s.next, c, tx⟩], next := s.next + 1 } else s
  | .approve c id tx =>
    if s.halted then s
    else match creqOf s id with
      | none => s
      | some r =>
        if c ∈ R.approvers ∧ c ≠ r.requester ∧ tx = r.tx then { s with approvals := s.approvals ++ [(id, c, tx)] }
        else s
  | .execute _ id =>
    if s.halted then s
    else match creqOf s id with
      | none => s
      | some r =>
        if (∃ ap ∈ s.approvals, ap.1 = id) ∧ id ∉ s.reserved ∧ s.spent + r.tx.amount ≤ cap then
          { s with reserved := s.reserved ++ [id], spent := s.spent + r.tx.amount }
        else s
  | .deliver id =>
    if s.halted then s
    else if id ∈ s.reserved then
      match creqOf s id with
      | none => s
      | some r => { s with delivery := s.delivery ++ [⟨id, r.tx, false⟩] }
    else s
  | .transmit i =>
    if s.halted then s
    else match s.delivery[i]? with
      | none => s
      | some d => if d.acked then s else { s with wire := s.wire ++ [(d.id, d.tx)], inflight := some i }
  | .bankProcess key =>
    match s.wire.find? (fun m => m.1 = key) with
    | none => s
    | some m => { s with bank := bankApply s.bank m.1 m.2 }
  | .ack i =>
    match s.delivery[i]? with
    | none => s
    | some d =>
      if d.id ∈ s.bank.map Prod.fst then ackSet s i d else s
  | .crash => { s with inflight := none }
  | .recover =>
    if recoverChecksHalt ∧ s.halted then s else { s with wire := s.wire ++ unacked s }
  | .halt c => if c ∈ R.admins then { s with halted := true } else s
  | .bankCall c key tx => if c ≠ R.gate then s else { s with bank := bankApply s.bank key tx }

def runC (R : Roles) (cap : ℕ) (rch : Bool) (s : CSt) (ops : List COp) : CSt := ops.foldl (stepC R cap rch) s

/-- untrusted concrete operations never carry the gate credential -/
def legalC (R : Roles) : COp → Prop
  | .bankCall c _ _ => c ≠ R.gate
  | _ => True



/-- durable tables ↦ model state; logged intents ↦ the model's `net` -/
def α (s : CSt) : St := ⟨s.next, s.reqs, s.approvals, s.reserved, s.spent, s.halted, s.bank,
  s.delivery.map (fun d => (d.id, d.tx))⟩

/-- the model operations matching one concrete step -/
def opsOf (s : CSt) : COp → List Op
  | .request c tx => [.request c tx]
  | .approve c id tx => [.approve c id tx]
  | .execute c id => [.execute c id]
  | .deliver id => [.deliver id]
  | .bankProcess key => if (s.wire.find? (fun m => m.1 = key)).isSome then [.arrive key] else []
  | .halt c => [.halt c]
  | .bankCall c key tx => [.bankCall c key tx]
  | _ => []

/-- the concrete invariant: transmitted messages are logged intents; logged intents carry their request's payload -/
structure CInv (s : CSt) : Prop where
  wire_logged : ∀ m ∈ s.wire, m ∈ (α s).net
  net_payload : ∀ m ∈ (α s).net, ∃ r, reqOf (α s) m.1 = some r ∧ r.tx = m.2

/-- the model trace matching a concrete trace -/
def absTrace (R : Roles) (cap : ℕ) : CSt → List COp → List Op
  | _, [] => []
  | s, o :: ops => opsOf s o ++ absTrace R cap (stepC R cap true s o) ops

def wTx : Tx := ⟨5, 10, 0⟩

/-- a halted gate with one logged intent that was never transmitted (stranded by the halt) -/
def strandedState : CSt := ⟨1, [⟨0, 1, wTx⟩], [(0, 2, wTx)], [0], 10, true, [⟨0, wTx, false⟩], none, [], []⟩

end ControlStack.SC26Refinement

