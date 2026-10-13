open ControlStack
open ControlStack.SC28
#check (ControlStack.SC28.halt_freezes : OrigFull)

theorem claim : Claim :=
by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intro admins G s ops _
  rfl

theorem witness : Witness :=
by
  unfold Witness
  decide
