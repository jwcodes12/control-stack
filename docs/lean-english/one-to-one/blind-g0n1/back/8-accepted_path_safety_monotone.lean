import ControlStack.Deployment.R2Contracts

namespace ControlStack.Deployment

def Back_accepted_path_safety_monotone : Prop :=
  ∀ (d larger : IR),
    (∀ e ∈ d.edges, e ∈ larger.edges) →
    d.nodes = larger.nodes → d.broker = larger.broker →
    d.receiver = larger.receiver → d.sink = larger.sink →
    d.database = larger.database → Accepted larger →
    ∀ a ∈ d.nodes, a.agent = true →
      ¬ AvoidedPath d a.id d.sink ∧ ¬ AvoidedPath d a.id d.database

end ControlStack.Deployment
