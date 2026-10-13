open ControlStack
open ControlStack.SC28
#check (ControlStack.SC28.revoked_lease_stops : OrigFull)

theorem claim : Claim :=
by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intro admins G C s lid ops _
  rfl

theorem witness : Witness :=
by
  unfold Witness
  decide
