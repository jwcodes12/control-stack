open ControlStack.SC19 ControlStack.AuthInstances ControlStack.AuthenticatedLog
theorem back_shape : Back_forged19_destroys_without_auth =
    BackPoint (authRun (step E0 full) (fun _ => none) init forged19).destroyed
      (authRun (step E0 full) claim19 init forged19).destroyed := rfl
theorem original_type : OrigPoint (authRun (step E0 full) (fun _ => none) init forged19).destroyed
    (authRun (step E0 full) claim19 init forged19).destroyed := forged19_destroys_without_auth
theorem claim : Claim := by intro withoutAuth withAuth; exact Iff.rfl
theorem witness : Witness := by simp only [Witness, ControlStack.AuthInstances.Back_forged19_destroys_without_auth]; decide
