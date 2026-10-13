open ControlStack
open ControlStack.SC16Refinement

theorem claim : Claim := ⟨Iff.rfl, fun _ _ _ => Iff.rfl⟩

theorem witness : Witness := by
  unfold Witness OrigAt SC16.Good SC16.DepOk SC16.ReviewOk
  decide
