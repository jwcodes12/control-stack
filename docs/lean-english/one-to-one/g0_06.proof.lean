open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro d r a approvers admins k tx
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (d : IR) (h : Accepted d) (r a : Node) (hr : r ∈ d.nodes) (rid : r.id = d.receiver) (ha : a ∈ d.nodes) (agent : a.agent = true) (approvers admins : List Nat) (k : Nat) (tx : SC26.Tx) : Orig d r a approvers admins k tx := agent_call_legal d h r a hr rid ha agent approvers admins k tx
