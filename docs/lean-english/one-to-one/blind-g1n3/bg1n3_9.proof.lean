open ControlStack.SC07Refinement

theorem original_signature : ∀ (K : CCfg) (ops : List COp) (w sink tolerance : ℕ), K.quotaRule = true → sink ≤ payloadIn (runC K cinit ops).fwd w → OriginalAt K ops w sink tolerance := by
  intro K ops w sink tolerance hK hsink
  exact sink_within_quota K hK ops w sink tolerance hsink

theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_⟩
  intro K ops w sink tolerance hK hsink
  rfl

theorem witness : Witness := by unfold Witness; decide
