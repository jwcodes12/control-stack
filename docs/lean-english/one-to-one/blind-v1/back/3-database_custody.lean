namespace ControlStack.Deployment

-- NOTE: Uses the real ControlStack.Deployment.Accepted predicate.
def Back_database_custody : Prop :=
  ∀ (d : IR) (e : Edge),
    ControlStack.Deployment.Accepted d →
    e ∈ d.edges → e.authority = true → e.target = d.database →
    e.source = d.receiver ∨ e.source = d.broker

end ControlStack.Deployment
