namespace ControlStack.SC18Refinement

def Back_concrete_durable : Prop :=
  ∀ (T : ℕ) (ops : List COp),
    let s := runC real T cinit ops
    ∀ r ∈ s.released,
      r.id ∈ (s.ackd.map Prod.fst).take r.llen ∧
      r.id ∈ s.sinkLog ∧
      r.clock ≤ r.lastAck + T

end ControlStack.SC18Refinement

namespace PL_bg4n2_2
open ControlStack.SC18Refinement ControlStack.SC18Liveness
def BackPoint (T : ℕ) (s : CSt) : Prop := ∀ r ∈ s.released,
  r.id ∈ (s.ackd.map Prod.fst).take r.llen ∧ r.id ∈ s.sinkLog ∧ r.clock ≤ r.lastAck + T
def OrigPoint (T : ℕ) (s : CSt) : Prop := ∀ r ∈ s.released,
  r.id ∈ (s.ackd.map Prod.fst).take r.llen ∧ r.id ∈ s.sinkLog ∧ r.clock ≤ r.lastAck + T
def Claim : Prop := ∀ T s, BackPoint T s ↔ OrigPoint T s
def Witness : Prop := (runC real 1 cinit [.arrive 0, .send 0, .commit 0, .ack 0, .release 0]).released = [⟨0, 1, 0, 0⟩] ∧
  (runC real 1 cinit [.arrive 0, .send 0, .commit 0, .ack 0, .release 0]).sinkLog = [0]

end PL_bg4n2_2
