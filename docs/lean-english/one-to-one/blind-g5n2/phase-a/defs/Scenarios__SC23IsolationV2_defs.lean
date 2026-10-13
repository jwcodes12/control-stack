-- EXCERPT of ControlStack/Scenarios/SC23IsolationV2.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC23IsolationV2

open ControlStack.Gate ControlStack.Authenticated

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
  /-- the planner's program: user inputs, its view of its own state, step index ↦ derived value -/
  plan : List ℕ → List PVal → ℕ → ℕ
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
  | userInput (caller v : ℕ)
  | toolResult (v : ℕ)
  | qtransform (i : ℕ)
  | derive
  | confirm (caller n tool : ℕ) (vals : List ℕ)
  | act (tool : ℕ) (idxs : List ℕ) (n : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  opaqueView : Bool
  taintCheck : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true⟩

def init : St := ⟨[], [], [], [], [], false⟩

def resolve (s : St) : PVal → Option ℕ
  | .trusted v => some v
  | .handle i => s.quarantine[i]?

/-- the leaky reveal: a handle shown as its content -/
def reveal (s : St) : PVal → PVal
  | .trusted v => .trusted v
  | .handle i => match s.quarantine[i]? with
    | some v => .trusted v
    | none => .handle i

/-- what the planner sees of its own state -/
def view (C : Checks) (s : St) : List PVal := if C.opaqueView then s.pvals else s.pvals.map (reveal s)

def argP (s : St) (idxs : List ℕ) : List PVal := idxs.filterMap (fun i => s.pvals[i]?)

def argV (s : St) (idxs : List ℕ) : List ℕ := (argP s idxs).filterMap (resolve s)

def confOf (s : St) (n : ℕ) : Option Conf := s.confs.find? (fun c => c.n = n)

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .userInput c v =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ E.users then { s with user := s.user ++ [v], pvals := s.pvals ++ [.trusted v] } else s
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
    if s.halted ∧ C.haltCheck then s
    else { s with pvals := s.pvals ++ [.trusted (E.plan s.user (view C s) s.pvals.length)] }
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

/-- the gate as a raw `Gate.System` (deployed checks) -/
def raw (E : Env) : System St Op Act := ⟨step E full, St.executed⟩

/-- the identity each operation claims -/
def claim : Op → Option ℕ
  | .userInput c _ => some c
  | .confirm c _ _ _ => some c
  | .halt c => some c
  | _ => none



def SameExceptContent (o o' : Op) : Prop := o = o' ∨ ∃ v v', o = .toolResult v ∧ o' = .toolResult v'

structure Rel (s t : St) : Prop where
  user : s.user = t.user
  pvals : s.pvals = t.pvals
  qlen : s.quarantine.length = t.quarantine.length
  halted : s.halted = t.halted

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
def ActOk (E : Env) (s : St) (x : Act) : Prop :=
  x.tool ∈ E.sensitive → x.tainted = true →
    ∃ n, x.conf = some n ∧ ∃ cf ∈ s.confs, cf.n = n ∧ cf.tool = x.tool ∧ cf.vals = x.vals ∧ cf.by_ ∈ E.users

structure Inv (E : Env) (s : St) : Prop where
  confs : ∀ cf ∈ s.confs, cf.by_ ∈ E.users
  exec : ∀ x ∈ s.executed, ActOk E s x

def spec (E : Env) : Spec (raw E) where
  Inv := Inv E
  ok := ActOk E
  step_inv := fun s o h => step_inv E s o h
  log_prefix := fun s o => executed_prefix E full s o
  inv_ok := fun _ h x hx => h.exec x hx

/-- the authenticated gate's spec, lifted by `Authenticated.authedSpec` -/
def specAuthed (E : Env) : Spec (authed (raw E) claim) := authedSpec (raw E) claim (spec E)



def trustedSum : List PVal → ℕ
  | [] => 0
  | .trusted v :: ps => v + trustedSum ps
  | .handle _ :: ps => trustedSum ps

def E0 : Env := ⟨[1], [9], [5], fun _ view _ => trustedSum view, fun v => v + 1⟩

/-- the forged trace: an untrusted issuer 9 delivers a tool result, a confirmation claiming user 1, and the action -/
def forged : List (ℕ × Op) := [(9, .toolResult 66), (9, .confirm 1 7 5 [66]), (9, .act 5 [0] 7)]

end ControlStack.SC23IsolationV2

