open ControlStack.SC26
open ControlStack.SC26Refinement
theorem original_signature : OrigEnvelope := by
  intro R cap ops hl
  exact concrete_safe R cap ops hl
theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_⟩
  intro R cap s
  exact Iff.rfl
theorem witness : Witness := by
  unfold Witness
  exact ⟨by simp [honestCOps, legalC], by decide⟩
