-- EXCERPT of ControlStack/Scenarios/SC18Refinement.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC18Refinement

open ControlStack.SC18Liveness



structure CFlags where
  failOpen : Bool
  promptReply : Bool
deriving DecidableEq, Repr

/-- the runtime's deployed configuration, with the scheduling premise `promptReply` -/
def real : CFlags := ⟨false, true⟩

structure CSt where
  clock : ℕ
  serving : Bool
  sinkUp : Bool
  /-- the runtime's `last_ack`: refreshed by record acks and by pings -/
  lastAck : ℕ
  /-- the clock of the last record ack (ghost; the abstract lastAck) -/
  recAck : ℕ
  seen : List ℕ
  sent : List ℕ
  /-- the sink's `fsync`'d record log -/
  sinkLog : List ℕ
  /-- record acks read by the proxy, with the clock at which each was read -/
  ackd : List (ℕ × ℕ)
  failed : List ℕ
  released : List SC18.Rel
deriving DecidableEq, Repr

inductive COp where
  | arrive (id : ℕ)
  | send (id : ℕ)
  | commit (id : ℕ)
  | ack (id : ℕ)
  | timeout (id : ℕ)
  | release (id : ℕ)
  | tick
  | ping
  | sinkCrash
  | sinkRestart
deriving DecidableEq, Repr

def cinit : CSt := ⟨0, true, true, 0, 0, [], [], [], [], [], []⟩

/-- the proxy reads the ack of `id`: sent, committed (the sink acks only after `fsync`), not read yet, not given up -/
def ackOk (s : CSt) (id : ℕ) : Prop :=
  id ∈ s.sent ∧ id ∈ s.sinkLog ∧ id ∉ s.ackd.map Prod.fst ∧ id ∉ s.failed

/-- the handler of `id` replies 200: fail-open on send; otherwise after its ack (within `T` of it under
`promptReply`); at most once -/
def relOk (F : CFlags) (T : ℕ) (s : CSt) (id : ℕ) : Prop :=
  ((F.failOpen = true ∧ id ∈ s.sent) ∨
    (F.failOpen = false ∧ ∃ p ∈ s.ackd, p.1 = id ∧ (F.promptReply = true → s.clock ≤ p.2 + T))) ∧
  id ∉ s.released.map SC18.Rel.id

def stepC (F : CFlags) (T : ℕ) (s : CSt) : COp → CSt
  | .arrive id => if s.serving = true ∧ id ∉ s.seen then { s with seen := s.seen ++ [id] } else s
  | .send id => if s.serving = true ∧ id ∈ s.seen ∧ id ∉ s.sent then { s with sent := s.sent ++ [id] } else s
  | .commit id =>
    if s.sinkUp = true ∧ id ∈ s.sent ∧ id ∉ s.sinkLog then { s with sinkLog := s.sinkLog ++ [id] } else s
  | .ack id =>
    if ackOk s id then { s with ackd := s.ackd ++ [(id, s.clock)], lastAck := s.clock, recAck := s.clock } else s
  | .timeout id =>
    if id ∈ s.sent ∧ id ∉ s.ackd.map Prod.fst ∧ id ∉ s.failed then { s with failed := s.failed ++ [id] } else s
  | .release id =>
    if relOk F T s id then { s with released := s.released ++ [⟨id, s.ackd.length, s.clock, s.recAck⟩] } else s
  | .tick =>
    if s.serving = true ∧ s.lastAck + T < s.clock + 1 then { s with clock := s.clock + 1, serving := false }
    else { s with clock := s.clock + 1 }
  | .ping => if s.sinkUp = true then { s with lastAck := s.clock, serving := true } else s
  | .sinkCrash => { s with sinkUp := false }
  | .sinkRestart => { s with sinkUp := true }

def runC (F : CFlags) (T : ℕ) (s : CSt) (ops : List COp) : CSt := ops.foldl (stepC F T) s

structure CInv (s : CSt) : Prop where
  sent_seen : ∀ x ∈ s.sent, x ∈ s.seen
  log_sent : ∀ x ∈ s.sinkLog, x ∈ s.sent
  ack_log : ∀ p ∈ s.ackd, p.1 ∈ s.sinkLog
  ack_time : ∀ p ∈ s.ackd, p.2 ≤ s.recAck
  rec_le : s.recAck ≤ s.clock
  failed_sent : ∀ x ∈ s.failed, x ∈ s.sent
  rel_ack : ∀ r ∈ s.released, r.id ∈ s.ackd.map Prod.fst

/-- α into the resumable-watchdog model -/
def α (T : ℕ) (s : CSt) : Resume.St :=
  ⟨s.seen, s.ackd.map Prod.fst, s.ackd.map Prod.fst, true, s.clock, s.recAck, decide (s.recAck + T < s.clock),
    s.released, false⟩

/-- the model steps matching one concrete event -/
def opsOf (T : ℕ) (s : CSt) : COp → List Resume.Op
  | .arrive id => if s.serving = true ∧ id ∉ s.seen then [.request id] else []
  | .ack id => if ackOk s id then [.logWrite id] else []
  | .release id => if relOk real T s id then [.release id] else []
  | .tick => [.tick]
  | _ => []

/-- the model trace of a concrete trace -/
def absTrace (T : ℕ) : CSt → List COp → List Resume.Op
  | _, [] => []
  | s, o :: ops => opsOf T s o ++ absTrace T (stepC real T s o) ops

end ControlStack.SC18Refinement

