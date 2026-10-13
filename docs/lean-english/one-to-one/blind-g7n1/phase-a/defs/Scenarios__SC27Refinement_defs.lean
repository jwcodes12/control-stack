-- EXCERPT of ControlStack/Scenarios/SC27Refinement.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC27Refinement

open ControlStack.SC27Chain (chainHead)
open ControlStack.SC27ExtensionOnly (Env)



/-- a record in the witness's own log; `g` is a ghost copy of the storage examined -/
inductive WRec where
  | anc (head n : ℕ) (g : List ℕ)
  | fork (head n anchoredHead anchoredN : ℕ) (g : List ℕ)
deriving DecidableEq, Repr

structure CSt where
  store : List ℕ
  pub : List ℕ
  /-- the witness's memory: (n₀, h₀) of its last anchor -/
  wlast : Option (ℕ × ℕ)
  /-- ghost: the last anchored list -/
  ghostLast : Option (List ℕ)
  wlog : List WRec
  accepted : List (List ℕ)
deriving DecidableEq, Repr

inductive COp where
  | append (e : ℕ)
  | rewrite (l : List ℕ)
  | publish (h : ℕ)
  | examine
  | verify (m : List ℕ)
deriving DecidableEq, Repr

def cinit : CSt := ⟨[], [], none, none, [], []⟩

/-- the anchor records of a witness log: (head, ghost list) -/
def ancs (l : List WRec) : List (ℕ × List ℕ) :=
  l.filterMap fun r => match r with
    | .anc h _ g => some (h, g)
    | _ => none

/-- the fork records of a witness log -/
def forks (l : List WRec) : List (List ℕ) :=
  l.filterMap fun r => match r with
    | .fork _ _ _ _ g => some g
    | _ => none

def anchorIt (E : Env) (s : CSt) : CSt :=
  { s with wlast := some (s.store.length, chainHead E.H E.h0 s.store), ghostLast := some s.store,
           wlog := s.wlog ++ [.anc (chainHead E.H E.h0 s.store) s.store.length s.store] }

def forkIt (E : Env) (s : CSt) (n0 h0 : ℕ) : CSt :=
  { s with wlog := s.wlog ++ [.fork (chainHead E.H E.h0 s.store) s.store.length h0 n0 s.store] }

/-- the witness's `examine` (witness.py), comparing chain heads -/
def examine (E : Env) (s : CSt) : CSt :=
  if s.store = [] then s
  else match s.wlast with
    | none => anchorIt E s
    | some (n0, h0) =>
      if s.store.length = n0 ∧ chainHead E.H E.h0 s.store = h0 then s
      else if s.store.length < n0 ∨ chainHead E.H E.h0 (s.store.take n0) ≠ h0 then forkIt E s n0 h0
      else anchorIt E s

/-- `trustWriter`: the `--writer-heads` control (false when deployed) -/
def stepC (E : Env) (trustWriter : Bool) (s : CSt) : COp → CSt
  | .append e => { s with store := s.store ++ [e] }
  | .rewrite l => { s with store := l }
  | .publish h => { s with pub := s.pub ++ [h] }
  | .examine => examine E s
  | .verify m =>
    if (∃ a ∈ ancs s.wlog, a.1 = chainHead E.H E.h0 m) ∨ (trustWriter = true ∧ chainHead E.H E.h0 m ∈ s.pub) then
      { s with accepted := s.accepted ++ [m] }
    else s

def runC (E : Env) (b : Bool) (s : CSt) (ops : List COp) : CSt := ops.foldl (stepC E b) s

/-- the witness's memory is the length and head of the (ghost) last anchored list -/
def CInv (E : Env) (s : CSt) : Prop := s.wlast = s.ghostLast.map (fun l => (l.length, chainHead E.H E.h0 l))

/-- collision resistance at an examine: injective on {last anchored list, the same-length prefix of storage} -/
def ExamInj (E : Env) (s : CSt) : Prop :=
  ∀ l0, s.ghostLast = some l0 → Set.InjOn (chainHead E.H E.h0) {l0, s.store.take l0.length}

/-- `ExamInj` at every examine of a (deployed) trace -/
def TraceInj (E : Env) : CSt → List COp → Prop
  | _, [] => True
  | s, o :: ops => (o = .examine → ExamInj E s) ∧ TraceInj E (stepC E false s o) ops

def α (s : CSt) : SC27ExtensionOnly.St := ⟨s.store, s.ghostLast, ancs s.wlog, forks s.wlog, s.accepted⟩

def opsOf (E : Env) (s : CSt) : COp → List SC27ExtensionOnly.Op
  | .append e => [.append e]
  | .rewrite l => [.rewrite l]
  | .publish _ => []
  | .examine =>
    if s.store = [] then []
    else match s.wlast with
      | none => [.anchor]
      | some (n0, h0) => if s.store.length = n0 ∧ chainHead E.H E.h0 s.store = h0 then [] else [.anchor]
  | .verify m => [.verify m]

def absTrace (E : Env) : CSt → List COp → List SC27ExtensionOnly.Op
  | _, [] => []
  | s, o :: ops => opsOf E s o ++ absTrace E (stepC E false s o) ops

def E0 : Env := SC27ExtensionOnly.E0

end ControlStack.SC27Refinement

