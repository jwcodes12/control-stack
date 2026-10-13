theorem original_type : OrigClosed := @ControlStack.AuthInstances.sc16_safe_authenticated

theorem hypotheses_iff (R : Roles) (U : List ℕ) : HypBack R U ↔ (HRev R U ∧ HApp R U) := by
  constructor
  · intro hb
    exact ⟨fun c hc => (hb c hc).1, fun c hc => (hb c hc).2⟩
  · rintro ⟨hr, ha⟩ c hc
    exact ⟨hr c hc, ha c hc⟩
theorem claim : Claim := by
  refine ⟨Iff.rfl, hypotheses_iff, ?_⟩
  intro R h U ops s
  unfold BackAt OrigAt
  constructor
  · rintro ⟨hg, hr, ha⟩
    refine ⟨hg, ?_, ?_⟩
    · intro rv hm
      obtain ⟨ho, hu, hp⟩ := hr rv hm
      exact ⟨rv.reviewer, .review rv.reviewer rv.d, ho, hu, rfl, rfl, hp⟩
    · intro ap hm
      obtain ⟨ho, hu, hp⟩ := ha ap hm
      exact ⟨ap.approver, .approve ap.approver ap.n ap.d ap.target ap.slot, ho, hu, rfl, rfl, hp⟩
  · rintro ⟨hg, hr, ha⟩
    refine ⟨hg, ?_, ?_⟩
    · intro rv hm
      obtain ⟨c, o, ho, hu, rfl, rfl, hp⟩ := hr rv hm
      exact ⟨ho, hu, hp⟩
    · intro ap hm
      obtain ⟨c, o, ho, hu, rfl, rfl, hp⟩ := ha ap hm
      exact ⟨ho, hu, hp⟩
theorem witness : Witness := by
  constructor
  · simp [HypBack, R0]
  · decide
