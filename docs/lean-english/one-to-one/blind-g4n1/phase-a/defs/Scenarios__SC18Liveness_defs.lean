-- EXCERPT of ControlStack/Scenarios/SC18Liveness.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC18Liveness

open ControlStack.SC18

variable (admins : List ℕ) (trusted T : ℕ)



structure Mono (s t : St) : Prop where
  reqs : s.reqs ⊆ t.reqs
  acked : s.acked ⊆ t.acked
  rel : s.released.map Rel.id ⊆ t.released.map Rel.id
  halt : s.halted = true → t.halted = true

namespace Resume

structure St where
  reqs : List ℕ
  acked : List ℕ
  logged : List ℕ
  sinkUp : Bool
  clock : ℕ
  lastAck : ℕ
  paused : Bool
  released : List SC18.Rel
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | request (id : ℕ)
  | logWrite (id : ℕ)
  | release (id : ℕ)
  | sinkDown
  | sinkRestore
  | tick
  | halt (caller : ℕ)
deriving DecidableEq, Repr

def init : St := ⟨[], [], [], true, 0, 0, false, [], false⟩

-- [line removed: names a claim under test]
def step (admins : List ℕ) (T : ℕ) (s : St) : Op → St
  | .request id => if s.halted then s else if id ∉ s.reqs then { s with reqs := s.reqs ++ [id] } else s
  | .logWrite id =>
    if s.halted then s
    else if id ∈ s.reqs ∧ s.sinkUp then
      { s with acked := s.acked ++ [id], logged := s.logged ++ [id], lastAck := s.clock, paused := false }
    else s
  | .release id =>
    if s.halted ∨ s.paused then s
    else if id ∈ s.reqs ∧ id ∉ s.released.map SC18.Rel.id ∧ id ∈ s.acked then
      { s with released := s.released ++ [⟨id, s.logged.length, s.clock, s.lastAck⟩] }
    else s
  | .sinkDown => { s with sinkUp := false }
  | .sinkRestore => { s with sinkUp := true }
  | .tick =>
    if s.halted then s
    else if s.lastAck + T < s.clock + 1 then { s with clock := s.clock + 1, paused := true }
    else { s with clock := s.clock + 1 }
  | .halt c => if c ∈ admins then { s with halted := true } else s

def run (admins : List ℕ) (T : ℕ) (s : St) (ops : List Op) : St := ops.foldl (step admins T) s

def RelOk (T : ℕ) (s : St) (r : SC18.Rel) : Prop :=
  r.llen ≤ s.logged.length ∧ r.id ∈ s.logged.take r.llen ∧ r.clock ≤ r.lastAck + T

structure Inv (T : ℕ) (s : St) : Prop where
  ack_ok : ∀ x ∈ s.acked, x ∈ s.logged
  rel_ok : ∀ r ∈ s.released, RelOk T s r
  nodup : (s.released.map SC18.Rel.id).Nodup
  clk : s.paused = false → s.clock ≤ s.lastAck + T

end Resume

end ControlStack.SC18Liveness

