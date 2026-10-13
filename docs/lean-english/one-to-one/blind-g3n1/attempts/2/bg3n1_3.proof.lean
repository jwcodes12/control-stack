open ControlStack
open ControlStack.SC15 ControlStack.AuthInstances ControlStack.AuthenticatedLog

theorem original_type : OrigClosed := @ControlStack.AuthInstances.sc15_safe_authenticated

theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_, ?_⟩
  · intro E U
    simp only [HypBack, HypOrig, List.mem_append, not_or]
  · intro E U ops s
    unfold BackAt OrigAt
    constructor
    · rintro ⟨hm, hr⟩
      refine ⟨hm, fun r h => ?_⟩
      obtain ⟨ho, hu, hp⟩ := hr r h
      exact ⟨r.reviewer, .review r.reviewer r.id r.sec, ho, hu, rfl, rfl, hp⟩
    · rintro ⟨hm, hr⟩
      refine ⟨hm, fun r h => ?_⟩
      obtain ⟨c, o, ho, hu, rfl, rfl, hp⟩ := hr r h
      exact ⟨ho, hu, hp⟩
theorem witness : Witness := by
  unfold Witness
  constructor
  · simp [HypBack, E0]
  · decide
