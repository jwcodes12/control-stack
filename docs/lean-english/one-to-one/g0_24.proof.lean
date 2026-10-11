open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract : Orig := TranscriptReplay.final_safe
