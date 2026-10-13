open ControlStack.SC26
theorem original_signature : OrigEnvelope := by
  intro R cap C ops hC hops
  exact safe_of_sound R cap hC ops hops
theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_⟩
  intro R cap s
  exact Iff.rfl
theorem witness : Witness := by
  unfold Witness
  exact ⟨sound_full, by simp [honestOps, legal], by decide⟩
