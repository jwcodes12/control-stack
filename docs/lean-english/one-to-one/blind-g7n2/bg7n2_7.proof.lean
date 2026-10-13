open ControlStack
open ControlStack.SC28Liveness
open ControlStack ControlStack.SC28
#check (ControlStack.SC28Liveness.honest_steps_progress : OrigFull)

theorem claim : Claim :=
by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intro admins G s w lid b units _ _ _ _ _ _
  rfl

theorem witness : Witness :=
by
  unfold Witness
  decide
