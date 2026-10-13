-- EXCERPT of ControlStack/Scenarios/SC27Chain.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC27Chain

open ControlStack.Gate

/-- the hash-chain head: each entry is hashed with the previous head -/
def chainHead (H : ℕ → ℕ → ℕ) (h0 : ℕ) (l : List ℕ) : ℕ := l.foldl H h0

structure Env where
  H : ℕ → ℕ → ℕ
  h0 : ℕ
  admins : List ℕ

structure St where
  /-- the writer-controlled storage -/
  log : List ℕ
  /-- ghost: what was really appended -/
  truth : List ℕ
  /-- (head, ghost copy of the anchored log if anchored by the independent witness; none if writer-published) -/
  anchors : List (ℕ × Option (List ℕ))
  accepted : List (List ℕ)
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | append (e : ℕ)
  | rewrite (l : List ℕ)
  | anchor
  | writerAnchor (hd : ℕ)
  | verify (m : List ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  anchorCheck : Bool
  independentOnly : Bool
  noSuffix : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init : St := ⟨[], [], [], [], false⟩

/-- the verifier's acceptance rule -/
abbrev Accepts (E : Env) (C : Checks) (s : St) (m : List ℕ) : Prop :=
  (∃ a ∈ s.anchors, a.1 = chainHead E.H E.h0 m ∧ (C.independentOnly = true → a.2.isSome = true)) ∨
  (C.anchorCheck = false ∧ chainHead E.H E.h0 m = chainHead E.H E.h0 s.log) ∨
  (C.noSuffix = false ∧ ∃ a ∈ s.anchors, a.2.isSome = true ∧
    ∃ k ∈ List.range (m.length + 1), a.1 = chainHead E.H E.h0 (m.take k))

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .append e => if s.halted ∧ C.haltCheck then s else { s with log := s.log ++ [e], truth := s.truth ++ [e] }
  | .rewrite l => if s.halted ∧ C.haltCheck then s else { s with log := l }
  | .anchor =>
    if s.halted ∧ C.haltCheck then s
    else { s with anchors := s.anchors ++ [(chainHead E.H E.h0 s.log, some s.log)] }
  | .writerAnchor hd => if s.halted ∧ C.haltCheck then s else { s with anchors := s.anchors ++ [(hd, none)] }
  | .verify m =>
    if s.halted ∧ C.haltCheck then s
    else if Accepts E C s m then { s with accepted := s.accepted ++ [m] } else s
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

/-- an accepted manifest whose chain head matches an independently anchored log -/
def AccOk (E : Env) (s : St) (m : List ℕ) : Prop :=
  ∃ a ∈ s.anchors, ∃ l, a.2 = some l ∧ chainHead E.H E.h0 l = chainHead E.H E.h0 m

structure Inv (E : Env) (s : St) : Prop where
  anc : ∀ a ∈ s.anchors, ∀ l, a.2 = some l → a.1 = chainHead E.H E.h0 l
  acc : ∀ m ∈ s.accepted, AccOk E s m

def sys (E : Env) : System St Op (List ℕ) where
  step := step E full
  effects := St.accepted

def spec (E : Env) : Spec (sys E) where
  Inv := Inv E
  ok := AccOk E
  step_inv := fun s o h => step_inv E s o h
  log_prefix := fun s o => accepted_prefix E full s o
  inv_ok := fun _ h m hm => h.acc m hm



def E0 : Env := ⟨fun h e => 100 * h + e + 1, 0, [9]⟩

end ControlStack.SC27Chain

