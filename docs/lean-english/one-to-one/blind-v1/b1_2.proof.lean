open ControlStack.Deployment

theorem original_type : ∀ (d : IR) (e : Edge), Accepted d → e ∈ d.edges → e.authority = true → e.target = d.sink →OrigConclusion d e := by
  intro d e h he ha ht
  exact ControlStack.Deployment.exclusive_sink d h e he ha ht

theorem claim : Claim := by
  constructor
  · exact Iff.rfl
  · intro d e h he ha ht
    exact Iff.rfl

theorem witness : Witness := by exact ⟨clean_accepted, by decide, rfl, rfl⟩
