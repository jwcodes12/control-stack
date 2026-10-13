open ControlStack ControlStack.Deployment

theorem original_signature : Orig := @path_edge_subset

theorem claim : Claim := by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intros
  exact Iff.rfl

theorem witness : Witness := by
  refine ⟨by decide, rfl, rfl, ?_, by decide, by decide⟩
  exact .step ⟨3,4,true,false,true⟩ (by decide) (by decide) (by decide) .refl
