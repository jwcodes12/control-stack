open ControlStack
open ControlStack.SC28Refinement
#check (ControlStack.SC28Refinement.exclusive_placement_safe : OrigFull)

theorem claim : Claim :=
by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intro G ops _
  rfl

theorem witness : Witness :=
by
  unfold Witness
  constructor
  · simp [isUnplaced]
  · decide
