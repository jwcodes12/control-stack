-- EXCERPT of ControlStack/Scenarios/SC07Refinement.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC07Refinement



/-- the gateway configuration: allowlisted (ip, port) pairs, the quota threshold, whether the quota rule exists -/
structure CCfg where
  allow : List (ℕ × ℕ)
  Q : ℕ
  quotaRule : Bool

/-- a forwarded upload packet (`fwd_up`): destination, payload bytes, on-wire IP length, window -/
structure FwdRec where
  ip : ℕ
  port : ℕ
  payload : ℕ
  wire : ℕ
  window : ℕ
deriving DecidableEq, Repr

structure CSt where
  halted : Bool
  /-- the named quota object's `consumed` bytes -/
  consumed : ℕ
  /-- ghost: the number of quota resets -/
  window : ℕ
  fwd : List FwdRec
  quotaDrop : ℕ
  denyDrop : ℕ
  haltDrop : ℕ
deriving DecidableEq, Repr

inductive COp where
  | pkt (ip port payload hdr : ℕ)
  | resetQuota
  | halt
deriving DecidableEq, Repr

def cinit : CSt := ⟨false, 0, 0, [], 0, 0, 0⟩

def stepC (K : CCfg) (s : CSt) : COp → CSt
  | .pkt ip port pl hd =>
    if s.halted then { s with haltDrop := s.haltDrop + 1 }
    else if (ip, port) ∈ K.allow then
      if K.quotaRule then
        if K.Q ≤ s.consumed + (pl + hd) then
          { s with consumed := s.consumed + (pl + hd), quotaDrop := s.quotaDrop + 1 }
        else { s with consumed := s.consumed + (pl + hd), fwd := s.fwd ++ [⟨ip, port, pl, pl + hd, s.window⟩] }
      else { s with fwd := s.fwd ++ [⟨ip, port, pl, pl + hd, s.window⟩] }
    else { s with denyDrop := s.denyDrop + 1 }
  | .resetQuota => if s.halted then { s with consumed := 0 } else { s with consumed := 0, window := s.window + 1 }
  | .halt => { s with halted := true }

def runC (K : CCfg) (s : CSt) (ops : List COp) : CSt := ops.foldl (stepC K) s

/-- forwarded payload bytes in window `w` -/
def payloadIn (l : List FwdRec) (w : ℕ) : ℕ := ((l.filter (fun r => r.window = w)).map FwdRec.payload).sum

/-- forwarded on-wire bytes in window `w` -/
def wireIn (l : List FwdRec) (w : ℕ) : ℕ := ((l.filter (fun r => r.window = w)).map FwdRec.wire).sum

structure CInv (s : CSt) : Prop where
  hdr : ∀ r ∈ s.fwd, r.payload ≤ r.wire
  wins : ∀ r ∈ s.fwd, r.window ≤ s.window
  cons : s.halted = false → wireIn s.fwd s.window ≤ s.consumed

/-- the model's environment: allowlist as `Nat.pair ip port`, quota `q = QUOTA − 1` payload bytes, admin 0 -/
def envOf (K : CCfg) : SC07Liveness.Env := ⟨K.allow.map (fun e => Nat.pair e.1 e.2), K.Q - 1, [0]⟩

def toFwd (r : FwdRec) : SC07Liveness.Fwd := ⟨Nat.pair r.ip r.port, r.payload, r.window⟩

def α (s : CSt) : SC07Liveness.St := ⟨s.window, payloadIn s.fwd s.window, s.fwd.map toFwd, s.halted⟩

def opsOf (K : CCfg) (s : CSt) : COp → List SC07Liveness.Op
  | .pkt ip port pl hd =>
    if s.halted = false ∧ (ip, port) ∈ K.allow ∧ s.consumed + (pl + hd) < K.Q then [.send (Nat.pair ip port) pl]
    else []
  | .resetQuota => [.tick]
  | .halt => [.halt 0]

def absTrace (K : CCfg) : CSt → List COp → List SC07Liveness.Op
  | _, [] => []
  | s, o :: ops => opsOf K s o ++ absTrace K (stepC K s o) ops

/-- QUOTA = 10; allowlisted 10.207.2.10:8080 as (1, 8080); not allowlisted (2, 8080) -/
def K0 (quotaRule : Bool) : CCfg := ⟨[(1, 8080)], 10, quotaRule⟩

end ControlStack.SC07Refinement

