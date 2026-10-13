-- EXCERPT of ControlStack/Scenarios/SC07Liveness.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC07Liveness

open ControlStack.Gate

structure Env where
  allow : List ℕ
  q : ℕ
  admins : List ℕ

/-- a forwarded send -/
structure Fwd where
  dest : ℕ
  bits : ℕ
  window : ℕ
deriving DecidableEq, Repr

structure St where
  window : ℕ
  used : ℕ
  log : List Fwd
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | send (dest n : ℕ)
  | tick
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  allowCheck : Bool
  quotaCheck : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true⟩

def init : St := ⟨0, 0, [], false⟩

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .send d n =>
    if s.halted ∧ C.haltCheck then s
    else if (C.allowCheck = true → d ∈ E.allow) ∧ (C.quotaCheck = true → s.used + n ≤ E.q) then
      { s with used := s.used + n, log := s.log ++ [⟨d, n, s.window⟩] }
    else s
  | .tick => if s.halted ∧ C.haltCheck then s else { s with window := s.window + 1, used := 0 }
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

/-- bits forwarded in window `w` -/
def wsum (s : St) (w : ℕ) : ℕ := ((s.log.filter (fun e => e.window = w)).map Fwd.bits).sum

def total (s : St) : ℕ := (s.log.map Fwd.bits).sum

structure Inv (E : Env) (s : St) : Prop where
  dests : ∀ e ∈ s.log, e.dest ∈ E.allow
  cur : wsum s s.window = s.used
  used_le : s.used ≤ E.q
  past : ∀ w, w < s.window → wsum s w ≤ E.q
  wins : ∀ e ∈ s.log, e.window ≤ s.window
  tot : total s ≤ E.q * s.window + s.used

def E0 : Env := ⟨[10], 8, [9]⟩

end ControlStack.SC07Liveness

