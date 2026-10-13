namespace ControlStack.Deployment

-- NOTE: Uses the real ControlStack.Deployment.Accepted predicate.
def Back_agent_not_receiver_uid : Prop :=
  ∀ (d : IR) (r a : Node),
    ControlStack.Deployment.Accepted d →
    r ∈ d.nodes → r.id = d.receiver →
    a ∈ d.nodes → a.agent = true →
    a.uid ≠ r.uid

end ControlStack.Deployment
