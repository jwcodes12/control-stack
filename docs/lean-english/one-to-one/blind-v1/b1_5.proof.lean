open ControlStack.Deployment

theorem original_type : ∀ (d : IR) (r a : Node), Accepted d → r ∈ d.nodes → r.id = d.receiver → a ∈ d.nodes → a.agent = true →OrigConclusion d r a := by
  intro d r a h hr hid ha hag
  exact ControlStack.Deployment.agent_not_receiver_uid d h r a hr hid ha hag

theorem claim : Claim := by
  constructor
  · exact Iff.rfl
  · intro d r a h hr hid ha hag
    exact Iff.rfl

theorem witness : Witness := by exact ⟨clean_accepted, by decide, rfl, by decide, rfl⟩
