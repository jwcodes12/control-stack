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
