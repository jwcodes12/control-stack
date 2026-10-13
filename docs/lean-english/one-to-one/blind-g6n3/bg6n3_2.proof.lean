open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26Liveness ControlStack.SC26Liveness.Concrete ControlStack.SC26LossyLiveness ControlStack.SC26LossyHalt

theorem pointwise : Pointwise := by
  intro R cap k ops₀ pre mid post d _ _ _ _ _
  unfold BackAt OrigAt
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  constructor
  · intro h
    exact ⟨List.count_pos_iff.mp (by omega), h⟩
  · exact And.right


theorem witness : Witness := by
  refine ⟨?_, by decide, ?_, by decide, by decide⟩
  · simp [setup, legalC]
  · simp [legalC]


theorem claim : Claim := ⟨pointwise, Iff.rfl, Iff.rfl⟩
