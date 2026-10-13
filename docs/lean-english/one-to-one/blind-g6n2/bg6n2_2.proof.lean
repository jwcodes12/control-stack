open ControlStack.SC26
theorem original_signature : OrigEnvelope := by
  intro R cap ops hd hl
  exact sc26_safe_disjoint R cap hd ops hl
theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_⟩
  intro R s
  exact Iff.rfl
theorem witness : Witness := by
  unfold Witness
  exact ⟨by simp [R0], by simp [honestOps, legal], by decide⟩
