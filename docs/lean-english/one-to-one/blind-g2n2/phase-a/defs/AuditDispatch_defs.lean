-- EXCERPT of ControlStack/AuditDispatch.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.AuditDispatch

structure St where
  requests : List ℕ
  audits : List ℕ
  effects : List ℕ

inductive Op where
  | request (id : ℕ)
  | appEvent
  | appSchema
  | dispatch (id : ℕ)
  | crash
  | restart

def step (s : St) : Op → St
  | .request id => { s with requests := s.requests ++ [id] }
  | .appEvent => s
  | .appSchema => s
  | .dispatch id =>
      if id ∈ s.requests ∧ id ∉ s.effects then
        { s with audits := s.audits ++ [id], effects := s.effects ++ [id] }
      else s
  | .crash => s
  | .restart => s

def run (s : St) (ops : List Op) : St := ops.foldl step s

/-- effect ⇒ audit, and the audit list is at least as long at every point the effect list grows -/
def Inv (s : St) : Prop := (∀ e ∈ s.effects, e ∈ s.audits) ∧ s.effects.Nodup

end ControlStack.AuditDispatch

