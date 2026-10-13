import ControlStack.Scenarios.SC17Infra

namespace ControlStack.SC17

-- A single reconcile step from any state that is not halted.
def Back_reconcile_restores : Prop :=
  ∀ (E : Env) (s : St),
    s.halted = false →
      (step E full s Op.reconcile).live =
        (step E full s Op.reconcile).desired

end ControlStack.SC17
