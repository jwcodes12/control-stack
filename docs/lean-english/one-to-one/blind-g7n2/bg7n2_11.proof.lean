open ControlStack
open ControlStack.SC28Refinement
#check (ControlStack.SC28Refinement.concrete_safe : OrigFull)

theorem claim : Claim :=
by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intro G s
  rfl

theorem witness : Witness :=
by
  unfold Witness
  decide
