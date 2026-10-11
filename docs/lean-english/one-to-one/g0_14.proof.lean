open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro larger start target
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (d larger : IR) (subset : ∀ e ∈ d.edges, e ∈ larger.edges) (broker : d.broker = larger.broker) (receiver : d.receiver = larger.receiver) (start target : Nat) (path : AvoidedPath d start target) : Orig larger start target := path_edge_subset d larger subset broker receiver start target path
