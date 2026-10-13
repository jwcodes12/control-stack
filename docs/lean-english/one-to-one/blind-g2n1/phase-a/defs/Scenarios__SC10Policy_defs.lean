-- EXCERPT of ControlStack/Scenarios/SC10Policy.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC10

open ControlStack.Gate

structure Env where
  admins : List ℕ
  h : ℕ → ℕ
  pinned : ℕ
  pinnedDigest : ℕ

/-- an enforcement decision: request, policy version used (none = not from the store), value used, store length then -/
structure Dec where
  req : ℕ
  ver : Option ℕ
  val : ℕ
  curLen : ℕ
deriving DecidableEq, Repr

structure St where
  /-- append-only policy log: (value, writer); the version is the index -/
  versions : List (ℕ × ℕ)
  cache : Option ℕ
  /-- an agent-writable policy file -/
  altFile : ℕ
  /-- the toolchain found through an agent-writable search path -/
  pathTool : ℕ
  decisions : List Dec
  builds : List ℕ
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | writePolicy (caller v : ℕ)
  | refresh
  | decide (req : ℕ)
  | writeAlt (v : ℕ)
  | altDecide (req : ℕ)
  | writePath (x : ℕ)
  | build
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  adminOnly : Bool
  fresh : Bool
  singleEval : Bool
  pinnedPath : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true, true⟩

def init : St := ⟨[], none, 0, 0, [], [], false⟩

def latest (s : St) : Option ℕ := if s.versions = [] then none else some (s.versions.length - 1)

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .writePolicy c v =>
    if s.halted ∧ C.haltCheck then s
    else if C.adminOnly = true → c ∈ E.admins then { s with versions := s.versions ++ [(v, c)] } else s
  | .refresh => if s.halted ∧ C.haltCheck then s else { s with cache := latest s }
  | .decide req =>
    if s.halted ∧ C.haltCheck then s
    else match (if C.fresh then latest s else s.cache) with
      | none => s
      | some i =>
        match s.versions[i]? with
        | none => s
        | some vw => { s with decisions := s.decisions ++ [⟨req, some i, vw.1, s.versions.length⟩] }
  | .writeAlt v => if s.halted ∧ C.haltCheck then s else { s with altFile := v }
  | .altDecide req =>
    if s.halted ∧ C.haltCheck then s
    else if C.singleEval then s
    else { s with decisions := s.decisions ++ [⟨req, none, s.altFile, s.versions.length⟩] }
  | .writePath x => if s.halted ∧ C.haltCheck then s else { s with pathTool := x }
  | .build =>
    if s.halted ∧ C.haltCheck then s
    else { s with builds := s.builds ++ [if C.pinnedPath then E.pinned else s.pathTool] }
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

/-- a decision that used the latest stored version at that moment, written by an admin -/
def DecOk (E : Env) (s : St) (d : Dec) : Prop :=
  ∃ i w, d.ver = some i ∧ s.versions[i]? = some (d.val, w) ∧ w ∈ E.admins ∧ i + 1 = d.curLen

structure Good (E : Env) (s : St) : Prop where
  decs : ∀ d ∈ s.decisions, DecOk E s d
  builds : ∀ b ∈ s.builds, E.h b = E.pinnedDigest

structure Inv (E : Env) (s : St) : Prop where
  vers : ∀ pv ∈ s.versions, pv.2 ∈ E.admins
  decs : ∀ d ∈ s.decisions, DecOk E s d
  builds : ∀ b ∈ s.builds, E.h b = E.pinnedDigest

def sys (E : Env) : System St Op Dec where
  step := step E full
  effects := St.decisions

def spec (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) : Spec (sys E) where
  Inv := Inv E
  ok := DecOk E
  step_inv := fun s o h => step_inv E hpin s o h
  log_prefix := fun s o => decisions_prefix E full s o
  inv_ok := fun _ h d hd => h.decs d hd



def E0 : Env := ⟨[9], id, 40, 40⟩

end ControlStack.SC10

