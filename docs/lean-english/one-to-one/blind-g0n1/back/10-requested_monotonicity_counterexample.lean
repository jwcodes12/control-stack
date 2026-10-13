import ControlStack.Deployment.R2Contracts

namespace ControlStack.Deployment

def Back_requested_monotonicity_counterexample : Prop :=
  sinkOnly.nodes = clean.nodes ∧
  (∀ e ∈ sinkOnly.edges, e ∈ clean.edges) ∧
  (∃ e ∈ sinkOnly.edges,
    e.source = sinkOnly.receiver ∧ e.target = sinkOnly.sink ∧ e.write = true) ∧
  Accepted clean ∧ ¬ Accepted sinkOnly

end ControlStack.Deployment
