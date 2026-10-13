open ControlStack
open ControlStack.SC16 ControlStack.SC16Disjoint

theorem original_type : OrigClosed := @ControlStack.SC16Disjoint.overlap_reviewer_is_agent

theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_, ?_⟩
  · intro s h
    obtain ⟨hd, hr⟩ := h
    refine ⟨?_, hr⟩
    exact ⟨⟨0, 5, 7⟩, by simp [hd], rfl, rfl⟩
  · refine ⟨{ init with deployed := [⟨99, 5, 7⟩], reviews := [⟨7, 2, 7, 1⟩] }, ?_⟩
    constructor
    · refine ⟨⟨⟨99, 5, 7⟩, by simp, rfl, rfl⟩, by decide, ?_⟩
      intro rv h
      simp only [List.mem_singleton] at h
      subst rv
      decide
    · unfold OrigAt
      decide
theorem witness : Witness := by
  unfold Witness
  refine ⟨by decide, by decide, ?_⟩
  intro s h
  obtain ⟨hd, hr⟩ := h
  exact ⟨⟨⟨0, 5, 7⟩, by simp [hd], rfl, rfl⟩, hr⟩
