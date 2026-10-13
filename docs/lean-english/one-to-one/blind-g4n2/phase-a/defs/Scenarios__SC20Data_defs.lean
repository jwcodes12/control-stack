-- EXCERPT of ControlStack/Scenarios/SC20Data.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC20

open ControlStack.Gate

structure Env where
  allow : List ℕ
  registry : ℕ → Option ℕ
  reviewers : List ℕ
  admins : List ℕ
  h : ℕ → ℕ

structure Ex where
  id : ℕ
  content : ℕ
  src : Option ℕ
  writer : ℕ
deriving DecidableEq, Repr

structure St where
  /-- newest version first -/
  store : List Ex
  /-- (example id, reviewer, digest promoted) -/
  promoted : List (ℕ × ℕ × ℕ)
  manifest : Option (List (ℕ × ℕ))
  /-- training runs: (example id, content used) -/
  trained : List (List (ℕ × ℕ))
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | ingest (src id x : ℕ)
  | agentWrite (caller id x : ℕ)
  | edit (id x : ℕ)
  | promote (caller id : ℕ)
  | freeze (caller : ℕ) (ids : List ℕ)
  | train
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  sourceCheck : Bool
  quarantine : Bool
  recheck : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init : St := ⟨[], [], none, [], false⟩

def exOf (s : St) (id : ℕ) : Option Ex := s.store.find? (fun e => e.id = id)

/-- may this example (by its current content) enter a frozen manifest? -/
def admitted (E : Env) (C : Checks) (s : St) (e : Ex) : Bool :=
  match e.src with
  | some src => !C.sourceCheck || (decide (src ∈ E.allow) && decide (E.registry e.id = some (E.h e.content)))
  | none => !C.quarantine || s.promoted.any (fun p => p.1 = e.id && p.2.2 = E.h e.content)

def manifestOf (E : Env) (C : Checks) (s : St) (ids : List ℕ) : List (ℕ × ℕ) :=
  ids.filterMap (fun i => (exOf s i).bind (fun e => if admitted E C s e then some (i, E.h e.content) else none))

/-- every manifest entry's current content still has the frozen digest -/
def intact (E : Env) (s : St) (m : List (ℕ × ℕ)) : Bool :=
  m.all (fun p => (exOf s p.1).any (fun e => E.h e.content = p.2))

def runOf (s : St) (m : List (ℕ × ℕ)) : List (ℕ × ℕ) := m.filterMap (fun p => (exOf s p.1).map (fun e => (p.1, e.content)))

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .ingest src id x => if s.halted ∧ C.haltCheck then s else { s with store := ⟨id, x, some src, 0⟩ :: s.store }
  | .agentWrite c id x => if s.halted ∧ C.haltCheck then s else { s with store := ⟨id, x, none, c⟩ :: s.store }
  | .edit id x =>
    if s.halted ∧ C.haltCheck then s
    else match exOf s id with
      | none => s
      | some e => { s with store := { e with content := x } :: s.store }
  | .promote c id =>
    if s.halted ∧ C.haltCheck then s
    else match exOf s id with
      | none => s
      | some e =>
        if c ∈ E.reviewers ∧ c ≠ e.writer ∧ e.src = none then
          { s with promoted := s.promoted ++ [(id, c, E.h e.content)] }
        else s
  | .freeze c ids =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ E.admins then { s with manifest := some (manifestOf E C s ids) } else s
  | .train =>
    if s.halted ∧ C.haltCheck then s
    else match s.manifest with
      | none => s
      | some m => if C.recheck = true → intact E s m = true then { s with trained := s.trained ++ [runOf s m] } else s
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

/-- a digest that is registered for the example, or that a reviewer promoted -/
def Adm (E : Env) (s : St) (i d : ℕ) : Prop :=
  E.registry i = some d ∨ ∃ p ∈ s.promoted, p.1 = i ∧ p.2.2 = d ∧ p.2.1 ∈ E.reviewers

def Good (E : Env) (s : St) : Prop := ∀ r ∈ s.trained, ∀ q ∈ r, Adm E s q.1 (E.h q.2)

structure Inv (E : Env) (s : St) : Prop where
  prom : ∀ p ∈ s.promoted, p.2.1 ∈ E.reviewers
  man : ∀ m, s.manifest = some m → ∀ q ∈ m, Adm E s q.1 q.2
  trained : Good E s

def sys (E : Env) : System St Op (List (ℕ × ℕ)) where
  step := step E full
  effects := St.trained

def spec (E : Env) : Spec (sys E) where
  Inv := Inv E
  ok := fun s r => ∀ q ∈ r, Adm E s q.1 (E.h q.2)
  step_inv := fun s o h => step_inv E s o h
  log_prefix := fun s o => trained_prefix E full s o
  inv_ok := fun _ h r hr => h.trained r hr



def E0 : Env := ⟨[50], fun i => if i = 0 then some 7 else none, [2], [9], id⟩

end ControlStack.SC20

