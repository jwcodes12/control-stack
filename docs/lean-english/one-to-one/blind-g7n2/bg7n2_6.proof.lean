open ControlStack
open ControlStack.AuthInstances
open ControlStack ControlStack.SC28
open ControlStack.AuthenticatedLog
#check (ControlStack.AuthInstances.forged28_consumes_without_auth : OrigFull)

theorem claim : Claim :=
by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  unfold BackResult OrigResult
  constructor <;> decide

theorem witness : Witness :=
by
  unfold Witness
  decide
