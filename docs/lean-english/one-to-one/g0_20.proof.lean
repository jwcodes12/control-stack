open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro R s t halted step
 have same : t = s := by
  cases step <;> first | rfl | simp_all [ControlStack.TrustedBroker.Allowed] | rw [← halted]
 constructor
 · intro h
   exact ControlStack.TrustedBroker.halted_absorbing R s t halted step
 · intro _
   exact same
 theorem witness : Witness := clean_accepted
