-- EXCERPT of ControlStack/Scenarios/SC18Logging.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC18

open ControlStack.Gate

/-- a released response: request id, trusted-log length, clock and last acknowledgement time at release -/
structure Rel where
  id : ℕ
  llen : ℕ
  clock : ℕ
  lastAck : ℕ
deriving DecidableEq, Repr

structure St where
  reqs : List ℕ
  /-- the node's view: records some sink acknowledged -/
  acked : List ℕ
  /-- the trusted sink's committed log -/
  logged : List ℕ
  cfg : ℕ
  sinkUp : Bool
  clock : ℕ
  lastAck : ℕ
  released : List Rel
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | request (id : ℕ)
  | logWrite (id : ℕ)
  | release (id : ℕ)
  | setSink (caller v : ℕ)
  | sinkDown
  | sinkRestore
  | tick
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  logFirst : Bool
  failOpen : Bool
  cfgProtect : Bool
  watchdog : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, false, true, true, true⟩

/-- the initial state: logging points at the trusted sink, which is up -/
def init (trusted : ℕ) : St := ⟨[], [], [], trusted, true, 0, 0, [], false⟩

def step (admins : List ℕ) (trusted T : ℕ) (C : Checks) (s : St) : Op → St
  | .request id =>
    if s.halted ∧ C.haltCheck then s else if id ∉ s.reqs then { s with reqs := s.reqs ++ [id] } else s
  | .logWrite id =>
    if s.halted ∧ C.haltCheck then s
    else if id ∈ s.reqs ∧ s.sinkUp then
      { s with acked := s.acked ++ [id], lastAck := s.clock,
               logged := if s.cfg = trusted then s.logged ++ [id] else s.logged }
    else s
  | .release id =>
    if s.halted ∧ C.haltCheck then s
    else if id ∈ s.reqs ∧ id ∉ s.released.map Rel.id ∧
        (C.logFirst → id ∈ s.acked ∨ (C.failOpen ∧ s.sinkUp = false)) then
      { s with released := s.released ++ [⟨id, s.logged.length, s.clock, s.lastAck⟩] }
    else s
  | .setSink c v =>
    if s.halted ∧ C.haltCheck then s else if C.cfgProtect → c ∈ admins then { s with cfg := v } else s
  | .sinkDown => { s with sinkUp := false }
  | .sinkRestore => { s with sinkUp := true }
  | .tick =>
    if s.halted ∧ C.haltCheck then s
    else if C.watchdog ∧ s.lastAck + T < s.clock + 1 then { s with clock := s.clock + 1, halted := true }
    else { s with clock := s.clock + 1 }
  | .halt c => if c ∈ admins then { s with halted := true } else s

def run (admins : List ℕ) (trusted T : ℕ) (C : Checks) (s : St) (ops : List Op) : St :=
  ops.foldl (step admins trusted T C) s

/-- premise: admins only ever point logging at the trusted sink -/
def legal (admins : List ℕ) (trusted : ℕ) : Op → Prop
  | .setSink c v => c ∈ admins → v = trusted
  | _ => True



/-- a release whose record was in the trusted log when it happened, within `T` ticks of the last acknowledgement -/
def RelOk (T : ℕ) (s : St) (r : Rel) : Prop :=
  r.llen ≤ s.logged.length ∧ r.id ∈ s.logged.take r.llen ∧ r.clock ≤ r.lastAck + T

def Good (T : ℕ) (s : St) : Prop := (∀ r ∈ s.released, RelOk T s r) ∧ (s.released.map Rel.id).Nodup

structure Inv (trusted T : ℕ) (s : St) : Prop where
  cfg_ok : s.cfg = trusted
  ack_ok : ∀ x ∈ s.acked, x ∈ s.logged
  rel_ok : ∀ r ∈ s.released, RelOk T s r
  nodup : (s.released.map Rel.id).Nodup
  clk : s.halted = false → s.clock ≤ s.lastAck + T

def sys (admins : List ℕ) (trusted T : ℕ) : System St {o : Op // legal admins trusted o} Rel where
  step := fun s o => step admins trusted T full s o.1
  effects := St.released

def spec (admins : List ℕ) (trusted T : ℕ) : Spec (sys admins trusted T) where
  Inv := Inv trusted T
  ok := RelOk T
  step_inv := fun s o h => step_inv admins trusted T s o.1 o.2 h
  log_prefix := fun s o => released_prefix admins trusted T full s o.1
  inv_ok := fun _ h r hr => h.rel_ok r hr



end ControlStack.SC18

