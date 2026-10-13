import ControlStack.Deployment.R2Contracts

namespace ControlStack.Deployment

def Back_path_edge_subset : Prop :=
  ∀ (d larger : IR) (start target : Nat),
    (∀ e ∈ d.edges, e ∈ larger.edges) →
    d.broker = larger.broker → d.receiver = larger.receiver →
    AvoidedPath d start target → AvoidedPath larger start target

end ControlStack.Deployment
