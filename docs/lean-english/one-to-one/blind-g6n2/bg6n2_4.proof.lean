open ControlStack.SC26
theorem original_signature : OrigEnvelope := by
  intro R cap s ops hh hl
  exact ControlStack.SC26.halt_freezes R cap s ops hl hh
theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_, ?_, ?_⟩
  · intro h R cap s ops hh hl
    obtain ⟨he, hb⟩ := h R cap s ops hh hl
    exact ⟨fun m => by rw [he], hb⟩
  · intro s t h
    exact ⟨fun m => by rw [h.1], h.2⟩
  · exact ⟨{ init with halted := true, net := [(0, tx1)] },
      { init with halted := true, net := [(0, tx1), (0, tx1)] },
      by decide, by simp [BackAt, init], by simp [OrigAt, init]⟩
theorem witness : Witness := by
  unfold Witness
  exact ⟨rfl, by simp [legal], rfl, rfl, by decide⟩
