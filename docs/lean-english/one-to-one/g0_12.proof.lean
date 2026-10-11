open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 let d : IR := {clean with edges := ⟨0,6,false,false,false⟩ :: clean.edges}
 have accepted : Accepted d := by decide
 have path : AvoidedPath d 0 6 := .step ⟨0,6,false,false,false⟩ (by decide) (by decide) (by decide) .refl
 intro h
 exact h d Witnesses.agentA 6 accepted (by decide) rfl (by decide) path
 theorem witness : Witness := clean_accepted
