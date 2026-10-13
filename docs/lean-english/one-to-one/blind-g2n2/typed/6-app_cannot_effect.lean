import ControlStack.AuditDispatch

namespace ControlStack.AuditDispatch

def Back_app_cannot_effect : Prop :=
  ∀ (s : St) (o : Op),
    (∀ id : ℕ, o ≠ Op.dispatch id) → (step s o).effects = s.effects

end ControlStack.AuditDispatch
