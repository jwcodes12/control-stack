open ControlStack
open ControlStack.SC28Liveness
open ControlStack ControlStack.SC28
#check (ControlStack.SC28Liveness.progress_interleaved : OrigFull)

theorem claim : Claim :=
by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  have step_report : ∀ (admins : List ℕ) (G : ℕ) (s : St) (w a r : ℕ),
      step admins G full s (.work w a r) = step admins G full s (.work w a a) := by
    intro admins G s w a r
    simp [step, charge, full]
  constructor
  · intro s w lid b a reported G
    simp [charge, full]
  · intro admins G s w lid b a reported p _ _ _ _
    dsimp only [BackResult, OrigResult]
    rw [step_report]

theorem witness : Witness :=
by
  unfold Witness
  decide
