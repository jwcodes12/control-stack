namespace ControlStack.SC18Refinement

-- Under α, the abstract logged list is the proxy's record-acknowledgement list.
-- r.lastAck records the last record-ack clock at release, excluding pings.
def Back_concrete_safe : Prop :=
  ∀ (T : ℕ) (ops : List COp),
    let s := α T (runC real T cinit ops)
    (∀ r ∈ s.released,
      r.id ∈ s.logged.take r.llen ∧ r.clock ≤ r.lastAck + T) ∧
    (s.released.map ControlStack.SC18.Rel.id).Nodup

end ControlStack.SC18Refinement

namespace PL_bg4n2_1
open ControlStack.SC18Refinement ControlStack.SC18Liveness
def BackPoint (T : ℕ) (c : CSt) : Prop :=
  let s := α T c
  (∀ r ∈ s.released, r.id ∈ s.logged.take r.llen ∧ r.clock ≤ r.lastAck + T) ∧
  (s.released.map ControlStack.SC18.Rel.id).Nodup
def OrigPoint (T : ℕ) (c : CSt) : Prop :=
  (∀ r ∈ c.released, Resume.RelOk T (α T c) r) ∧
  (c.released.map ControlStack.SC18.Rel.id).Nodup
def Claim : Prop := ∀ T ops, BackPoint T (runC real T cinit ops) ↔ OrigPoint T (runC real T cinit ops)
def Witness : Prop := (runC real 1 cinit [.arrive 0, .send 0, .commit 0, .ack 0, .release 0]).released = [⟨0, 1, 0, 0⟩]

end PL_bg4n2_1
