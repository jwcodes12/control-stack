/-! Source-only adversarial theorem-scope controls; not runtime refinement. -/
import ControlStack.Scenarios.SC25Audit
import ControlStack.Scenarios.SC26Transaction

namespace FidelityScope

open ControlStack.SC25

/-- A `halt_freezes` statement about executed effects is not a claim
that all volatile state is preserved: a later crash clears checked. -/
example :
    let pre : St := run R0 id cls0 full init
      [.submit 1 0 50 false, .audit 2 0 true, .check 0, .halt 4]
    pre.checked = [0] ∧
    (step R0 id cls0 full pre .crash).checked = [] ∧
    (step R0 id cls0 full pre .crash).executed = pre.executed := by
  decide

/-- The *formal legality hypothesis* of SC26.safe is only about direct
bank calls. It does not say whether an approve caller's identity is authentic.
That must be implemented and independently evaluated outside this model. -/
example (R : ControlStack.SC26.Roles) (caller id : ℕ)
    (payload : ControlStack.SC26.Tx) :
    ControlStack.SC26.legal R (.approve caller id payload) := by
  trivial

end FidelityScope

#print axioms ControlStack.SC25.sc25_safe
#print axioms ControlStack.SC25.halt_freezes
#print axioms ControlStack.SC26.sc26_safe
