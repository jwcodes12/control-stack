open ControlStack ControlStack.AuditDispatch
example : FrozenBack = (∀ (s : St) (ops : List Op), Inv s → BackAt s ops) := rfl
example (s : St) (ops : List Op) (h : Inv s) : OrigAt s ops := trace_safe s ops h

theorem claim : Claim := by
  intro s ops h
  exact Iff.rfl

theorem witness : Witness := by
  refine ⟨⟨[1], [1], [1]⟩,
    [.request 2, .appEvent, .appSchema, .dispatch 2, .dispatch 2, .crash, .restart], ?_, ?_⟩
  · simp [ControlStack.AuditDispatch.Inv]
  · decide
