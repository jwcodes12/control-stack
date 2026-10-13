open ControlStack.SC26
open ControlStack.SC26Refinement
theorem original_signature : OrigEnvelope := by
  intro R cap s ops hh hl
  exact concrete_halt R cap s ops hl hh
theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_⟩
  intro s t
  exact Iff.rfl
theorem witness : Witness := by
  unfold Witness
  exact ⟨rfl, by simp [legalC], rfl, rfl, by decide⟩
