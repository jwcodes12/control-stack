-- EXCERPT of ControlStack/Scenarios/SC27ExtensionOnly.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC27ExtensionOnly

open ControlStack.SC27Chain (chainHead)

structure Env where
  H : ℕ → ℕ → ℕ
  h0 : ℕ

structure St where
  log : List ℕ
  last : Option (List ℕ)
  /-- (head, ghost copy of the anchored log), oldest first -/
  anchors : List (ℕ × List ℕ)
  alarms : List (List ℕ)
  accepted : List (List ℕ)
deriving DecidableEq, Repr

inductive Op where
  | append (e : ℕ)
  | rewrite (l : List ℕ)
  | anchor
  | verify (m : List ℕ)
deriving DecidableEq, Repr

def init : St := ⟨[], none, [], [], []⟩

/-- does the current storage extend the last anchored state? -/
def extendsLast (s : St) : Bool := match s.last with
  | none => true
  | some l0 => l0.isPrefixOf s.log

def doAnchor (E : Env) (s : St) : St :=
  { s with last := some s.log, anchors := s.anchors ++ [(chainHead E.H E.h0 s.log, s.log)] }

/-- `extOnly`: the extension-only witness (deployed); `false`: anchor whatever storage holds -/
def step (E : Env) (extOnly : Bool) (s : St) : Op → St
  | .append e => { s with log := s.log ++ [e] }
  | .rewrite l => { s with log := l }
  | .anchor =>
    if extOnly then (if extendsLast s then doAnchor E s else { s with alarms := s.alarms ++ [s.log] })
    else doAnchor E s
  | .verify m =>
    if ∃ a ∈ s.anchors, a.1 = chainHead E.H E.h0 m then { s with accepted := s.accepted ++ [m] } else s

def run (E : Env) (extOnly : Bool) (s : St) (ops : List Op) : St := ops.foldl (step E extOnly) s

structure Inv (E : Env) (s : St) : Prop where
  heads : ∀ a ∈ s.anchors, a.1 = chainHead E.H E.h0 a.2
  chain : s.anchors.Pairwise (fun a b => a.2 <+: b.2)
  toLast : ∀ a ∈ s.anchors, ∃ l, s.last = some l ∧ a.2 <+: l
  lastAnch : ∀ l, s.last = some l → ∃ a ∈ s.anchors, a.2 = l
  acc : ∀ m ∈ s.accepted, ∃ a ∈ s.anchors, a.1 = chainHead E.H E.h0 m

def E0 : Env := ⟨fun h e => 100 * h + e + 1, 0⟩

end ControlStack.SC27ExtensionOnly

