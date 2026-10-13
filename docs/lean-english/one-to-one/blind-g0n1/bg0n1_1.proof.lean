open ControlStack ControlStack.Deployment

theorem original_signature : Orig := @runtime_exclusive

theorem claim : Claim := by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intros
  exact Iff.rfl

theorem witness : Witness := by
  exact ⟨clean_accepted, ControlStack.Deployment.Witnesses.extracted.authority, ControlStack.Deployment.Witnesses.extracted.receiverNode, ⟨⟨3,4,true,false,true⟩, by decide, rfl, rfl⟩⟩
