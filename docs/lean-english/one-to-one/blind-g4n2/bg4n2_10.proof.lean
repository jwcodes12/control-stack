open ControlStack.SC20 ControlStack.AuthInstances ControlStack.AuthenticatedLog
theorem back_shape : Back_forged20_trains_without_auth =
    BackPoint (authRun (step E0 full) (fun _ => none) init forged20).trained
      (authRun (step E0 full) claim20 init forged20).trained := rfl
theorem original_type : OrigPoint (authRun (step E0 full) (fun _ => none) init forged20).trained
    (authRun (step E0 full) claim20 init forged20).trained := forged20_trains_without_auth
theorem claim : Claim := by intro withoutAuth withAuth; exact Iff.rfl
theorem witness : Witness := by simp only [Witness, ControlStack.AuthInstances.Back_forged20_trains_without_auth]; decide
