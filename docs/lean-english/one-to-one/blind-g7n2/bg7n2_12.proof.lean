open ControlStack
open ControlStack.SC28Refinement
#check (ControlStack.SC28Refinement.concrete_revoked_stops : OrigFull)

theorem claim : Claim :=
by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intro G lid first second _
  unfold BackResult OrigResult
  rw [runC_append]

theorem witness : Witness :=
by
  unfold Witness
  decide
