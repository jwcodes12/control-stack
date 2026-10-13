namespace ControlStack.Deployment

-- NOTE: Uses the real ControlStack.Deployment.Accepted predicate.
-- AvoidedPath is the supplied relation, including its zero-step path.
def Back_accepted_no_avoided_path : Prop :=
  ∀ (d : IR) (a : Node),
    ControlStack.Deployment.Accepted d →
    a ∈ d.nodes → a.agent = true →
    (¬ ControlStack.Deployment.AvoidedPath d a.id d.sink) ∧
    (¬ ControlStack.Deployment.AvoidedPath d a.id d.database)

end ControlStack.Deployment
