-- EXCERPT of ControlStack/Scenarios/SC23Injection.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC23

open ControlStack.Gate

structure Policy where
  users : List ℕ
  admins : List ℕ
  sensitive : List ℕ

/-- a stored value: id, content, implementation label, ghost provenance -/
structure Val where
  id : ℕ
  v : ℕ
  label : Bool
  prov : Bool
deriving DecidableEq, Repr

/-- a user confirmation: nonce, tool, exact argument values shown, confirming principal -/
structure Conf where
  n : ℕ
  tool : ℕ
  vals : List ℕ
  by_ : ℕ
deriving DecidableEq, Repr

/-- an executed action: tool, argument values, ghost provenance of the arguments, confirmation used -/
structure Act where
  tool : ℕ
  vals : List ℕ
  prov : Bool
  conf : Option ℕ
deriving DecidableEq, Repr

structure St where
  store : List Val
  confs : List Conf
  used : List ℕ
  executed : List Act
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | userInput (id v : ℕ)
  | toolResult (id v : ℕ)
  | derive (id : ℕ) (srcs : List ℕ) (v : ℕ)
  | confirm (caller n tool : ℕ) (vals : List ℕ)
  | act (tool : ℕ) (args : List ℕ) (n : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  propagate : Bool
  taintCheck : Bool
  exact : Bool
  oneUse : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true, true⟩

def init : St := ⟨[], [], [], [], false⟩

def valOf (s : St) (id : ℕ) : Option Val := s.store.find? (fun x => x.id = id)

def argsOf (s : St) (args : List ℕ) : List Val := args.filterMap (valOf s)

def confOf (s : St) (n : ℕ) : Option Conf := s.confs.find? (fun c => c.n = n)

def anyLabel (xs : List Val) : Bool := xs.any (fun x => x.label)
def anyProv (xs : List Val) : Bool := xs.any (fun x => x.prov)

def doExec (s : St) (a : Act) (u : List ℕ) : St := { s with executed := s.executed ++ [a], used := s.used ++ u }

def step (P : Policy) (C : Checks) (s : St) : Op → St
  | .userInput id v =>
    if s.halted ∧ C.haltCheck then s
    else if valOf s id = none then { s with store := s.store ++ [⟨id, v, false, false⟩] } else s
  | .toolResult id v =>
    if s.halted ∧ C.haltCheck then s
    else if valOf s id = none then { s with store := s.store ++ [⟨id, v, true, true⟩] } else s
  | .derive id srcs v =>
    if s.halted ∧ C.haltCheck then s
    else if valOf s id = none ∧ (argsOf s srcs).length = srcs.length then
      { s with store := s.store ++
          [⟨id, v, if C.propagate then anyLabel (argsOf s srcs) else false, anyProv (argsOf s srcs)⟩] }
    else s
  | .confirm c n tool vals =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ P.users ∧ confOf s n = none then { s with confs := s.confs ++ [⟨n, tool, vals, c⟩] } else s
  | .act tool args n =>
    if s.halted ∧ C.haltCheck then s
    else if (argsOf s args).length ≠ args.length then s
    else if tool ∉ P.sensitive ∨ (C.taintCheck = true → anyLabel (argsOf s args) = false) then
      doExec s ⟨tool, (argsOf s args).map Val.v, anyProv (argsOf s args), none⟩ []
    else match confOf s n with
      | none => s
      | some cf =>
        if cf.tool = tool ∧ (C.exact = true → cf.vals = (argsOf s args).map Val.v) ∧ (C.oneUse = true → n ∉ s.used)
        then doExec s ⟨tool, (argsOf s args).map Val.v, anyProv (argsOf s args), some n⟩ [n]
        else s
  | .halt c => if c ∈ P.admins then { s with halted := true } else s

def run (P : Policy) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step P C) s

/-- a sensitive action whose arguments truly depend on untrusted data was confirmed exactly by a user -/
def ActOk (P : Policy) (s : St) (a : Act) : Prop :=
  a.tool ∈ P.sensitive → a.prov = true →
    ∃ n, a.conf = some n ∧ ∃ cf ∈ s.confs, cf.n = n ∧ cf.tool = a.tool ∧ cf.vals = a.vals ∧ cf.by_ ∈ P.users

def Good (P : Policy) (s : St) : Prop :=
  (∀ a ∈ s.executed, ActOk P s a) ∧ (s.executed.filterMap Act.conf).Nodup

structure Inv (P : Policy) (s : St) : Prop where
  lab : ∀ x ∈ s.store, x.label = x.prov
  conf_by : ∀ cf ∈ s.confs, cf.by_ ∈ P.users
  exec : ∀ a ∈ s.executed, a.tool ∈ P.sensitive → a.prov = true →
    ∃ n, a.conf = some n ∧ ∃ cf ∈ s.confs, cf.n = n ∧ cf.tool = a.tool ∧ cf.vals = a.vals
  conf_used : ∀ a ∈ s.executed, ∀ n, a.conf = some n → n ∈ s.used
  nodup : (s.executed.filterMap Act.conf).Nodup

def sys (P : Policy) : System St Op Act where
  step := step P full
  effects := St.executed

def spec (P : Policy) : Spec (sys P) where
  Inv := Inv P
  ok := ActOk P
  step_inv := fun s o hi => step_inv P s o hi
  log_prefix := fun s o => executed_prefix P full s o
  inv_ok := fun _ hi a ha => hi.good.1 a ha



def P0 : Policy := ⟨[1], [9], [5]⟩

end ControlStack.SC23

