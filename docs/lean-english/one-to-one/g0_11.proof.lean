open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro d R cap ops actual sinkEffects
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (d : IR) (r : Node) (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) (actual : List Edge) (sinkEffects : List (Nat × SC26.Tx)) (h : Accepted d) (ext : ExtractionFaithful d r actual) (ref : ProtocolRefinement d r R cap ops sinkEffects) : Orig d R cap ops actual sinkEffects := deployment_safe d r R cap ops actual sinkEffects h ext ref
