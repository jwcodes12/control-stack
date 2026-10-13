open ControlStack.Deployment.TranscriptReplay

theorem original_type : OrigConclusion := by
  exact ControlStack.Deployment.TranscriptReplay.runtime_trace

theorem claim : Claim := by
  constructor
  · exact Iff.rfl
  · exact Iff.rfl

theorem witness : Witness := by exact ⟨final_counts.1, final_counts.2.2.1⟩
