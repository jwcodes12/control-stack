open ControlStack.Deployment

theorem original_type : ∀ (d : IR) (a : Node), Accepted d → a ∈ d.nodes → a.agent = true →OrigConclusion d a := by
  intro d a h ha hag
  exact ControlStack.Deployment.accepted_no_avoided_path d h a ha hag

theorem claim : Claim := by
  constructor
  · exact Iff.rfl
  · intro d a h ha hag
    exact Iff.rfl

theorem witness : Witness := by exact ⟨clean_accepted, by decide, rfl⟩
