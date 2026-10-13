-- EXCERPT of ControlStack/Scenarios/SC17Drift.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC17Drift

structure St where
  desired : List ℕ
  live : List ℕ
  /-- ghost: out-of-band grants since the last reconcile, with birth times -/
  drift : List (ℕ × ℕ)
  clock : ℕ
  lastRec : ℕ
  /-- out-of-band mutations admitted in the current tick -/
  tickOob : ℕ
deriving DecidableEq, Repr

inductive Op where
  | oob (g : ℕ)
  | tick
  | reconcile
deriving DecidableEq, Repr

def init (desired : List ℕ) : St := ⟨desired, desired, [], 0, 0, 0⟩

def doReconcile (s : St) (t : ℕ) : St := { s with live := s.desired, drift := [], lastRec := t }

/-- `d`: out-of-band mutations per tick (environment premise); `W`: reconcile period; `sched`: the scheduler is on -/
def step (d W : ℕ) (sched : Bool) (s : St) : Op → St
  | .oob g =>
    if s.tickOob < d then { s with live := g :: s.live, drift := (g, s.clock) :: s.drift, tickOob := s.tickOob + 1 }
    else s
  | .tick =>
    if sched ∧ s.lastRec + W ≤ s.clock + 1 then { doReconcile s (s.clock + 1) with clock := s.clock + 1, tickOob := 0 }
    else { s with clock := s.clock + 1, tickOob := 0 }
  | .reconcile => doReconcile s s.clock

def run (d W : ℕ) (sched : Bool) (s : St) (ops : List Op) : St := ops.foldl (step d W sched) s

structure Inv (d W : ℕ) (s : St) : Prop where
  live_eq : s.live = s.drift.map Prod.fst ++ s.desired
  births : ∀ p ∈ s.drift, s.lastRec ≤ p.2 ∧ p.2 ≤ s.clock
  rec_le : s.lastRec ≤ s.clock
  period : s.clock < s.lastRec + W
  count : s.drift.length ≤ d * (s.clock - s.lastRec) + s.tickOob
  tick_le : s.tickOob ≤ d

end ControlStack.SC17Drift

