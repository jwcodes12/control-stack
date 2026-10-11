open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro d actual e
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (d : IR) (actual : List Edge) (h : Accepted d) (faithful : Faithful d actual) (e : Edge) (member : e ∈ actual) (authority : e.authority = true) (sink : e.target = d.sink) : Orig d actual e := runtime_exclusive d actual h faithful e member authority sink
