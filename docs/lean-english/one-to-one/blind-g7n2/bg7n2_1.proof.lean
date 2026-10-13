open ControlStack
open ControlStack.SC28
#check (ControlStack.SC28.sc28_safe : OrigFull)

theorem claim : Claim :=
by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intro admins G ops _
  rfl

theorem witness : Witness :=
by
  unfold Witness
  constructor
  · simp [legal]
  · decide
