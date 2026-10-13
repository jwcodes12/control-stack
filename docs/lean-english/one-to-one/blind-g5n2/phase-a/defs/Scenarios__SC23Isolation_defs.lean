-- EXCERPT of ControlStack/Scenarios/SC23Isolation.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC23Isolation

open ControlStack.Gate

/-- a planner value: trusted content, or an opaque handle to a quarantined value -/
inductive PVal where
  | trusted (v : ℕ)
  | handle (i : ℕ)
deriving DecidableEq, Repr

def PVal.isHandle : PVal → Bool
  | .trusted _ => false
  | .handle _ => true

structure Env where
  users : List ℕ
  admins : List ℕ
  sensitive : List ℕ
  /-- the planner's program: trusted inputs and step index ↦ derived value -/
  plan : List ℕ → ℕ → ℕ
  /-- the quarantined transformer -/
  qf : ℕ → ℕ

structure Conf where
  n : ℕ
  tool : ℕ
  vals : List ℕ
  by_ : ℕ
deriving DecidableEq, Repr

structure Act where
  tool : ℕ
  vals : List ℕ
  tainted : Bool
  conf : Option ℕ
deriving DecidableEq, Repr

structure St where
  user : List ℕ
  quarantine : List ℕ
  pvals : List PVal
  confs : List Conf
  executed : List Act
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | userInput (v : ℕ)
  | toolResult (v : ℕ)
  | qtransform (i : ℕ)
  | derive
  | plannerRead (i : ℕ)
  | confirm (caller n tool : ℕ) (vals : List ℕ)
  | act (tool : ℕ) (idxs : List ℕ) (n : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  isolation : Bool
  taintCheck : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true⟩

def init : St := ⟨[], [], [], [], [], false⟩

def resolve (s : St) : PVal → Option ℕ
  | .trusted v => some v
  | .handle i => s.quarantine[i]?

def argP (s : St) (idxs : List ℕ) : List PVal := idxs.filterMap (fun i => s.pvals[i]?)

def argV (s : St) (idxs : List ℕ) : List ℕ := (argP s idxs).filterMap (resolve s)

def confOf (s : St) (n : ℕ) : Option Conf := s.confs.find? (fun c => c.n = n)

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .userInput v =>
    if s.halted ∧ C.haltCheck then s else { s with user := s.user ++ [v], pvals := s.pvals ++ [.trusted v] }
  | .toolResult v =>
    if s.halted ∧ C.haltCheck then s
    else { s with quarantine := s.quarantine ++ [v], pvals := s.pvals ++ [.handle s.quarantine.length] }
  | .qtransform i =>
    if s.halted ∧ C.haltCheck then s
    else match s.quarantine[i]? with
      | none => s
      | some v =>
        { s with quarantine := s.quarantine ++ [E.qf v], pvals := s.pvals ++ [.handle s.quarantine.length] }
  | .derive =>
    if s.halted ∧ C.haltCheck then s else { s with pvals := s.pvals ++ [.trusted (E.plan s.user s.pvals.length)] }
  | .plannerRead i =>
    if s.halted ∧ C.haltCheck then s
    else if C.isolation then s
    else match s.quarantine[i]? with
      | none => s
      | some v => { s with pvals := s.pvals ++ [.trusted v] }
  | .confirm c n tool vals =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ E.users ∧ confOf s n = none then { s with confs := s.confs ++ [⟨n, tool, vals, c⟩] } else s
  | .act tool idxs n =>
    if s.halted ∧ C.haltCheck then s
    else if (argP s idxs).length ≠ idxs.length ∨ (argV s idxs).length ≠ idxs.length then s
    else if tool ∉ E.sensitive ∨ (C.taintCheck = true → (argP s idxs).any PVal.isHandle = false) then
      { s with executed := s.executed ++ [⟨tool, argV s idxs, (argP s idxs).any PVal.isHandle, none⟩] }
    else match confOf s n with
      | none => s
      | some cf =>
        if cf.tool = tool ∧ cf.vals = argV s idxs then
          { s with executed := s.executed ++ [⟨tool, argV s idxs, (argP s idxs).any PVal.isHandle, some n⟩] }
        else s
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

/-- two operations that are equal except for tool-result content -/
def SameExceptContent : Op → Op → Prop
  | .toolResult _, .toolResult _ => True
  | o, o' => o = o'

/-- the planner-visible part of the state -/
structure Rel (s t : St) : Prop where
  user : s.user = t.user
  pvals : s.pvals = t.pvals
  qlen : s.quarantine.length = t.quarantine.length
  halted : s.halted = t.halted

def ActOk (E : Env) (s : St) (x : Act) : Prop :=
  x.tool ∈ E.sensitive → x.tainted = true →
    ∃ n, x.conf = some n ∧ ∃ cf ∈ s.confs, cf.n = n ∧ cf.tool = x.tool ∧ cf.vals = x.vals ∧ cf.by_ ∈ E.users

structure Inv (E : Env) (s : St) : Prop where
  confs : ∀ cf ∈ s.confs, cf.by_ ∈ E.users
  exec : ∀ x ∈ s.executed, ActOk E s x

def sys (E : Env) : System St Op Act where
  step := step E full
  effects := St.executed

def spec (E : Env) : Spec (sys E) where
  Inv := Inv E
  ok := ActOk E
  step_inv := fun s o h => step_inv E s o h
  log_prefix := fun s o => executed_prefix E full s o
  inv_ok := fun _ h x hx => h.exec x hx



def E0 : Env := ⟨[1], [9], [5], fun u k => 40 + u.length + k, fun v => v + 1⟩

end ControlStack.SC23Isolation

