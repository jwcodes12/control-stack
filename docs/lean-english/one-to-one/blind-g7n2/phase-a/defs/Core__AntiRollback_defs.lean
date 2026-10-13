-- EXCERPT of ControlStack/Core/AntiRollback.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.AntiRollback

open ControlStack.Gate

variable {St Op Eff : Type}

/-- a store record: version, state, predecessor state (the digest chain), and the op that produced it -/
structure Rec (St Op : Type) where
  ver : ℕ
  st : St
  prev : St
  op : Option Op
deriving DecidableEq, Repr

structure RSt (St Op Eff : Type) where
  /-- the durable store (may be rolled back) -/
  store : Rec St Op
  /-- every record ever written: the operator's backups -/
  hist : List (Rec St Op)
  /-- the trusted monotonic anchor: the last committed record -/
  anchor : Rec St Op
  /-- volatile fail-closed flag -/
  halted : Bool
  /-- ghost: the committed ops, in order -/
  committed : List Op
  /-- the effects released to the world (only at commit) -/
  released : List Eff
deriving DecidableEq, Repr

inductive ROp (Op : Type) where
  | write (o : Op)
  | bump
  | restart
  | rollback (k : ℕ)
deriving DecidableEq, Repr

def genesis (init : St) : Rec St Op := ⟨0, init, init, none⟩

def rinit (G : System St Op Eff) (init : St) : RSt St Op Eff :=
  ⟨genesis init, [genesis init], genesis init, false, [], G.effects init⟩

/-- the store is exactly the next record after the anchor -/
def IsNext (s : RSt St Op Eff) : Prop := s.store.ver = s.anchor.ver + 1 ∧ s.store.prev = s.anchor.st ∧ s.store.op ≠ none

/-- commit the store record: advance the anchor, release the effects its op produced (relative to its predecessor) -/
def commit (G : System St Op Eff) (s : RSt St Op Eff) : RSt St Op Eff :=
  { s with anchor := s.store, committed := s.committed ++ s.store.op.toList,
           released := s.released ++ (G.effects s.store.st).drop (G.effects s.store.prev).length, halted := false }

variable [DecidableEq St] [DecidableEq Op]

def stepR (G : System St Op Eff) (check : Bool) (s : RSt St Op Eff) : ROp Op → RSt St Op Eff
  | .write o =>
    if s.halted then s
    else if check = false ∨ s.store = s.anchor then
      let r : Rec St Op := ⟨s.anchor.ver + 1, G.step s.store.st o, s.store.st, some o⟩
      { s with store := r, hist := s.hist ++ [r] }
    else { s with halted := true }
  | .bump =>
    if s.halted then s
    else if check = false ∨ IsNext s then commit G s else s
  | .restart =>
    if check = false ∨ s.store = s.anchor then { s with halted := false }
    else if IsNext s then commit G s
    else { s with halted := true }
  | .rollback k =>
    match s.hist[k]? with
    | none => s
    | some r => { s with store := r }

def runR (G : System St Op Eff) (check : Bool) (s : RSt St Op Eff) (ops : List (ROp Op)) : RSt St Op Eff :=
  ops.foldl (stepR G check) s



/-- the invariant: backups are honest records (state = step of predecessor by its op); the store is a backup; the
anchor is the plain run of the committed ops and its effects are exactly the released ones -/
structure RInv (G : System St Op Eff) (S : Spec G) (init : St) (s : RSt St Op Eff) : Prop where
  hist_ok : ∀ r ∈ s.hist, r = genesis init ∨ ∃ o, r.op = some o ∧ r.st = G.step r.prev o
  store_mem : s.store ∈ s.hist
  anchor_run : s.anchor.st = G.run init s.committed
  released_eq : s.released = G.effects s.anchor.st
  anchor_ver : s.anchor.ver = s.committed.length
  inv : S.Inv s.anchor.st

omit [DecidableEq St] [DecidableEq Op] in
/-- an honest schedule item: commit an op; or crash after the write and restart (recovery); or a bare restart -/
inductive HItem (Op : Type) where
  | exec (o : Op)
  | crash (o : Op)
  | restart

def expand : HItem Op → List (ROp Op)
  | .exec o => [.write o, .bump]
  | .crash o => [.write o, .restart]
  | .restart => [.restart]

def hops : HItem Op → List Op
  | .exec o => [o]
  | .crash o => [o]
  | .restart => []

/-- a one-use nonce gate: the state is the list of used nonces, its effects are those uses -/
def nonceGate : System (List ℕ) ℕ ℕ where
  step := fun s n => if n ∈ s then s else s ++ [n]
  effects := id

/-- use nonce 0, commit; restore the genesis backup; use nonce 0 again, commit -/
def replayTrace : List (ROp ℕ) := [.write 0, .bump, .rollback 0, .write 0, .bump]

/-- SC-28's work steps under the anchor (legal ops only; storage rollback is now the adversary's `rollback`) -/
abbrev G28 := SC28.sys [9] 10

def w28 (o : SC28.Op) (h : SC28.legal o) : ROp {o : SC28.Op // SC28.legal o} := .write ⟨o, h⟩

/-- issue a 10-unit lease, assign it, consume 10; restore the backup taken before the work; consume 10 again -/
def spendTrace : List (ROp {o : SC28.Op // SC28.legal o}) :=
  [w28 (.issue 9 0 10) trivial, .bump, w28 (.assignTo 9 1 0) trivial, .bump, w28 (.work 1 10 10) trivial, .bump,
   .rollback 2, w28 (.work 1 10 10) trivial, .bump]

end ControlStack.AntiRollback

