-- EXCERPT of ControlStack/Core/AuthenticatedLog.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.AuthenticatedLog

open ControlStack.Gate ControlStack.Authenticated

variable {St Op R : Type}

/-- the authenticated run of a step function (effects are irrelevant here) -/
def authRun (step : St → Op → St) (claim : Op → Option ℕ) (s : St) (ops : List (ℕ × Op)) : St :=
  (authed (⟨step, fun _ => ([] : List Unit)⟩ : System St Op Unit) claim).run s ops

end ControlStack.AuthenticatedLog

