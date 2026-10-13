-- EXCERPT of ControlStack/Scenarios/SC06Artifacts.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC06

open ControlStack.Gate

structure Policy where
  users : List ℕ
  admins : List ℕ
  sensitive : List ℕ

structure Art where
  id : ℕ
  writer : ℕ
  typed : ℕ
  free : Option ℕ
deriving DecidableEq, Repr

/-- a value in an agent's context: owner, value, written by another agent?, free text? -/
structure Ctx where
  agent : ℕ
  val : ℕ
  fromOther : Bool
  free : Bool
deriving DecidableEq, Repr

structure Conf where
  n : ℕ
  agent : ℕ
  tool : ℕ
  val : ℕ
  by_ : ℕ
deriving DecidableEq, Repr

structure Act where
  agent : ℕ
  tool : ℕ
  val : ℕ
  fromOther : Bool
  conf : Option ℕ
deriving DecidableEq, Repr

structure St where
  arts : List Art
  ctx : List Ctx
  confs : List Conf
  executed : List Act
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | writeTyped (caller id x txt : ℕ)
  | writeRaw (caller id x txt : ℕ)
  | read (agent id : ℕ)
  | confirm (caller n agent tool val : ℕ)
  | act (agent tool val n : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  canon : Bool
  singlePath : Bool
  provCheck : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init : St := ⟨[], [], [], [], false⟩

def artOf (s : St) (id : ℕ) : Option Art := s.arts.find? (fun a => a.id = id)
def ctxOf (s : St) (r v : ℕ) : Option Ctx := s.ctx.find? (fun e => e.agent = r ∧ e.val = v)
def confOf (s : St) (n : ℕ) : Option Conf := s.confs.find? (fun c => c.n = n)

/-- the context entries a read produces -/
def readEntries (r : ℕ) (a : Art) : List Ctx :=
  ⟨r, a.typed, a.writer ≠ r, false⟩ :: (match a.free with | none => [] | some t => [⟨r, t, a.writer ≠ r, true⟩])

def step (P : Policy) (C : Checks) (s : St) : Op → St
  | .writeTyped c id x txt =>
    if s.halted ∧ C.haltCheck then s
    else { s with arts := ⟨id, c, x, if C.canon then none else some txt⟩ :: s.arts }
  | .writeRaw c id x txt =>
    if s.halted ∧ C.haltCheck then s
    else if C.singlePath then s else { s with arts := ⟨id, c, x, some txt⟩ :: s.arts }
  | .read r id =>
    if s.halted ∧ C.haltCheck then s
    else match artOf s id with
      | none => s
      | some a => { s with ctx := s.ctx ++ readEntries r a }
  | .confirm c n r tool v =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ P.users ∧ confOf s n = none then { s with confs := s.confs ++ [⟨n, r, tool, v, c⟩] } else s
  | .act r tool v n =>
    if s.halted ∧ C.haltCheck then s
    else match ctxOf s r v with
      | none => s
      | some e =>
        if tool ∉ P.sensitive ∨ ¬ (C.provCheck = true ∧ e.fromOther = true) then
          { s with executed := s.executed ++ [⟨r, tool, v, e.fromOther, none⟩] }
        else match confOf s n with
          | none => s
          | some cf =>
            if cf.agent = r ∧ cf.tool = tool ∧ cf.val = v then
              { s with executed := s.executed ++ [⟨r, tool, v, e.fromOther, some n⟩] }
            else s
  | .halt c => if c ∈ P.admins then { s with halted := true } else s

def run (P : Policy) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step P C) s

def ActOk (P : Policy) (s : St) (x : Act) : Prop :=
  x.tool ∈ P.sensitive → x.fromOther = true →
    ∃ n, x.conf = some n ∧ ∃ cf ∈ s.confs, cf.n = n ∧ cf.agent = x.agent ∧ cf.tool = x.tool ∧ cf.val = x.val ∧
      cf.by_ ∈ P.users

def Good (P : Policy) (s : St) : Prop := (∀ e ∈ s.ctx, e.free = false) ∧ ∀ x ∈ s.executed, ActOk P s x

structure Inv (P : Policy) (s : St) : Prop where
  arts : ∀ a ∈ s.arts, a.free = none
  ctx : ∀ e ∈ s.ctx, e.free = false
  confs : ∀ cf ∈ s.confs, cf.by_ ∈ P.users
  exec : ∀ x ∈ s.executed, ActOk P s x

def sys (P : Policy) : System St Op Act where
  step := step P full
  effects := St.executed

def spec (P : Policy) : Spec (sys P) where
  Inv := Inv P
  ok := ActOk P
  step_inv := fun s o h => step_inv P s o h
  log_prefix := fun s o => executed_prefix P full s o
  inv_ok := fun _ h x hx => h.exec x hx



def P0 : Policy := ⟨[5], [9], [7]⟩

end ControlStack.SC06

