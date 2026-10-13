import ControlStack.Scenarios.SC18Refinement

namespace ControlStack.SC18Refinement

def Back_concrete_durable : Prop :=
  ∀ (T : ℕ) (ops : List COp),
    let s := runC real T cinit ops
    ∀ r ∈ s.released,
      r.id ∈ (s.ackd.map Prod.fst).take r.llen ∧
      r.id ∈ s.sinkLog ∧
      r.clock ≤ r.lastAck + T

end ControlStack.SC18Refinement
