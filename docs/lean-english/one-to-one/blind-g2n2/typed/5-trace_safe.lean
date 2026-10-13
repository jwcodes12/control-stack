import ControlStack.AuditDispatch

namespace ControlStack.AuditDispatch

def Back_trace_safe : Prop :=
  ∀ (s : St) (ops : List Op),
    Inv s → Inv (run s ops) ∧ s.audits <+: (run s ops).audits

end ControlStack.AuditDispatch
