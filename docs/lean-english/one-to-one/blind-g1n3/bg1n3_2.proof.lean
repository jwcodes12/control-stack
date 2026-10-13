open ControlStack.SC07Exfil

theorem original_signature : ∀ q : ℕ, 0 < q → OriginalAt q := by
  intro q hq
  exact observable_schedule_exfil q hq

theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_⟩
  intro q hq
  simp [BackAt, OriginalAt, capped]

theorem witness : Witness := by norm_num [Witness, survive]
