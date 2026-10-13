open ControlStack ControlStack.Deployment

theorem original_signature : Orig := @deployment_safe

theorem claim : Claim := by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intros
  exact Iff.rfl

theorem witness : Witness := by
  exact ⟨clean_accepted, ControlStack.Deployment.Witnesses.extracted, ControlStack.Deployment.Witnesses.sc26_refined, rfl⟩
