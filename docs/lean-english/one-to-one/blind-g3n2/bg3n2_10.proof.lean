open ControlStack
open ControlStack.AuthInstances

theorem claim : Claim := Iff.rfl

theorem witness : Witness := by
  unfold Witness BackClosed
  decide
