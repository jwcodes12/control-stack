open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro d a
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (d larger : IR) (subset : ∀ e ∈ d.edges, e ∈ larger.edges) (nodes : d.nodes = larger.nodes) (broker : d.broker = larger.broker) (receiver : d.receiver = larger.receiver) (sink : d.sink = larger.sink) (database : d.database = larger.database) (accepted : Accepted larger) (a : Node) (member : a ∈ d.nodes) (agent : a.agent = true) : Orig d a := accepted_path_safety_monotone d larger subset nodes broker receiver sink database accepted a member agent
