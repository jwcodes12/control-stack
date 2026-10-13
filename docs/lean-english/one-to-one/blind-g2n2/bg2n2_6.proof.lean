open ControlStack ControlStack.AuditDispatch
example : FrozenBack = (∀ (s : St) (o : Op),
    (∀ id : ℕ, o ≠ Op.dispatch id) → BackAt s o) := rfl
example (s : St) (o : Op) (happ : ∀ id : ℕ, o ≠ Op.dispatch id) :
    OrigAt s o := app_cannot_effect s o happ

theorem claim : Claim := by
  intro s o happ
  exact Iff.rfl

theorem witness : Witness := by
  refine ⟨⟨[], [3], [3]⟩, .request 4, ?_, rfl, rfl, rfl⟩
  intro id h
  cases h
