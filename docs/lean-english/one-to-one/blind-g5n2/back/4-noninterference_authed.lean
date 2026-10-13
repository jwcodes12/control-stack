import ControlStack.Scenarios.SC23IsolationV2

namespace ControlStack.SC23IsolationV2

open ControlStack.Authenticated ControlStack.Gate

-- Authentication is supplied by authed and claim; the per-position relation
-- preserves issuers as well as every operation field except tool-result content.
def Back_noninterference_authed : Prop :=
  ∀ (E : Env) (ops ops' : List (ℕ × Op)),
    List.Forall₂
      (fun io io' => io.1 = io'.1 ∧ SameExceptContent io.2 io'.2)
      ops ops' →
      Rel ((authed (raw E) claim).run init ops)
        ((authed (raw E) claim).run init ops')

end ControlStack.SC23IsolationV2
