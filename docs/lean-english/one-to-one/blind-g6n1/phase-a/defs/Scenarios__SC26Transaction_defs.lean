-- EXCERPT of ControlStack/Scenarios/SC26Transaction.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC26

open ControlStack.Gate

/-- a transaction payload: destination account, amount, memo digest -/
structure Tx where
  dest : ℕ
  amount : ℕ
  memo : ℕ
deriving DecidableEq, Repr

/-- trusted role assignment (by OS identity); `gate` is the gate's own credential, the only one the bank accepts -/
structure Roles where
  agents : List ℕ
  approvers : List ℕ
  admins : List ℕ
  gate : ℕ

structure Req where
  id : ℕ
  requester : ℕ
  tx : Tx
deriving DecidableEq, Repr

structure St where
  next : ℕ
  reqs : List Req
  /-- (request id, approver, payload the approver approved) -/
  approvals : List (ℕ × ℕ × Tx)
  reserved : List ℕ
  spent : ℕ
  halted : Bool
  /-- the external system's ledger: (idempotency key, payload) -/
  bank : List (ℕ × Tx)
  /-- messages the gate has sent to the external system; each may arrive any number of times, at any later time -/
  net : List (ℕ × Tx)
deriving DecidableEq, Repr

inductive Op where
  | request (caller : ℕ) (tx : Tx)
  | approve (caller : ℕ) (id : ℕ) (tx : Tx)
  | execute (caller : ℕ) (id : ℕ)
  /-- the gate (re)sends a reserved transaction to the external system: first attempt, retry or crash recovery -/
  | deliver (id : ℕ)
  /-- the external system processes a message in flight (not under the gate's control; not stopped by HALT) -/
  | arrive (key : ℕ)
  /-- a direct call to the external system by `caller` -/
  | bankCall (caller : ℕ) (key : ℕ) (tx : Tx)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

/-- which checks the implementation performs; `full` is the deployed configuration -/
structure Checks where
  distinct : Bool
  payload : Bool
  nonce : Bool
  cap : Bool
  haltCheck : Bool
  bankDedup : Bool
  bankAuth : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true, true, true, true⟩

/-- the checks the SAFETY property needs. The gate-side nonce and the halt check are not among them: with an
idempotent receiver, uniqueness of effects comes from the receiver (adversarial review, Opus 5.5, D4). -/
structure Sound (C : Checks) : Prop where
  distinct : C.distinct = true
  payload : C.payload = true
  cap : C.cap = true
  dedup : C.bankDedup = true
  auth : C.bankAuth = true

def init : St := ⟨0, [], [], [], 0, false, [], []⟩

def reqOf (s : St) (id : ℕ) : Option Req := s.reqs.find? (fun r => r.id = id)

/-- the external system appends an entry unless (when idempotent) the key is already present -/
def bankAppend (C : Checks) (s : St) (key : ℕ) (tx : Tx) : St :=
  if C.bankDedup ∧ key ∈ s.bank.map Prod.fst then s else { s with bank := s.bank ++ [(key, tx)] }

def step (R : Roles) (cap : ℕ) (C : Checks) (s : St) : Op → St
  | .request c tx =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ R.agents then { s with reqs := s.reqs ++ [⟨s.next, c, tx⟩], next := s.next + 1 } else s
  | .approve c id tx =>
    if s.halted ∧ C.haltCheck then s
    else match reqOf s id with
      | none => s
      | some r =>
        if c ∈ R.approvers ∧ (C.distinct → c ≠ r.requester) ∧ (C.payload → tx = r.tx) then
          { s with approvals := s.approvals ++ [(id, c, tx)] }
        else s
  | .execute _ id =>
    if s.halted ∧ C.haltCheck then s
    else match reqOf s id with
      | none => s
      | some r =>
        if (∃ ap ∈ s.approvals, ap.1 = id) ∧ (C.nonce → id ∉ s.reserved) ∧ (C.cap → s.spent + r.tx.amount ≤ cap) then
          { s with reserved := s.reserved ++ [id], spent := s.spent + r.tx.amount }
        else s
  | .deliver id =>
    if s.halted ∧ C.haltCheck then s
    else if id ∈ s.reserved then
      match reqOf s id with
      | none => s
      | some r => { s with net := s.net ++ [(id, r.tx)] }
    else s
  | .arrive key =>
    match s.net.find? (fun m => m.1 = key) with
    | none => s
    | some m => bankAppend C s m.1 m.2
  | .bankCall c key tx => if C.bankAuth ∧ c ≠ R.gate then s else bankAppend C s key tx
  | .halt c => if c ∈ R.admins then { s with halted := true } else s

def run (R : Roles) (cap : ℕ) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step R cap C) s

/-- untrusted operations never carry the gate's credential (credential separation, a correspondence premise) -/
def legal (R : Roles) : Op → Prop
  | .bankCall c _ _ => c ≠ R.gate
  | _ => True



/-- an approval of exactly `r`'s payload, by an approver who is not `r`'s requester -/
def Approved (R : Roles) (s : St) (k : ℕ) (r : Req) : Prop :=
  ∃ a, (k, a, r.tx) ∈ s.approvals ∧ a ∈ R.approvers ∧ a ≠ r.requester

def amt (s : St) (k : ℕ) : ℕ := ((reqOf s k).map (fun r => r.tx.amount)).getD 0

structure Inv (R : Roles) (cap : ℕ) (s : St) : Prop where
  appr_ok : ∀ ap ∈ s.approvals, ∃ r, reqOf s ap.1 = some r ∧ ap.2.2 = r.tx ∧ ap.2.1 ∈ R.approvers ∧
    ap.2.1 ≠ r.requester
  res_ok : ∀ k ∈ s.reserved, ∃ r, reqOf s k = some r ∧ Approved R s k r
  spent_eq : s.spent = (s.reserved.map (amt s)).sum
  spent_le : s.spent ≤ cap
  bank_ok : ∀ e ∈ s.bank, e.1 ∈ s.reserved ∧ ∃ r, reqOf s e.1 = some r ∧ r.tx = e.2
  bank_nodup : (s.bank.map Prod.fst).Nodup
  net_ok : ∀ m ∈ s.net, m.1 ∈ s.reserved ∧ ∃ r, reqOf s m.1 = some r ∧ r.tx = m.2

/-- the safety property: every effect is exactly approved, keys are unique, the total is within the cap -/
def Good (R : Roles) (cap : ℕ) (s : St) : Prop :=
  (∀ e ∈ s.bank, ∃ r, reqOf s e.1 = some r ∧ r.tx = e.2 ∧ e.1 ∈ s.reserved ∧ Approved R s e.1 r) ∧
  (s.bank.map Prod.fst).Nodup ∧ (s.bank.map (fun e => e.2.amount)).sum ≤ cap

/-- states whose request lookups and approvals extend `s`'s -/
structure Ext (s t : St) : Prop where
  req : ∀ k r, reqOf s k = some r → reqOf t k = some r
  appr : s.approvals ⊆ t.approvals

/-- the SC-26 gate as a `Gate.System` over legal operations; its effect log is the bank ledger -/
def sys (R : Roles) (cap : ℕ) : System St {o : Op // legal R o} (ℕ × Tx) where
  step := fun s o => step R cap full s o.1
  effects := St.bank

def spec (R : Roles) (cap : ℕ) : Spec (sys R cap) where
  Inv := Inv R cap
  ok := fun s e => ∃ r, reqOf s e.1 = some r ∧ r.tx = e.2 ∧ e.1 ∈ s.reserved ∧ Approved R s e.1 r
  step_inv := fun s o h => step_inv R cap sound_full s o.1 o.2 h
  log_prefix := fun s o => bank_prefix R cap full s o.1
  inv_ok := fun _ h e he => h.good.1 e he



def R0 : Roles := ⟨[1], [2], [3], 9⟩
def tx1 : Tx := ⟨5, 10, 0⟩
def tx2 : Tx := ⟨6, 10, 0⟩

def R1 : Roles := ⟨[1], [1], [3], 9⟩

end ControlStack.SC26

