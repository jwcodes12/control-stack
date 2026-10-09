/-
SC-06 approval multiplicity witness (2026-10-09).

Source target: ControlStack/Scenarios/SC06Artifacts.lean on main.
This is not a contradiction of sc06_safe: ActOk requires existence of an
exactly matching trusted-user confirmation, not a distinct / consumed one for
each irreversible effect. It is a counterexample to a stronger *single-use*
reading of "needs user confirmation".

Agent 1 writes a typed value; agent 2 reads it and executes the same sensitive
action twice using one user confirmation number. SC06.full has all checks on.

No claim is made about the frozen harness behavior or a deployed payment gate;
the model's executed list stands for its abstract effects, and the runtime may
ask a user again. Model-to-runtime correspondence remains unresolved.
-/
import ControlStack.Scenarios.SC06Artifacts

namespace ControlStack.SC06ConfirmationReuse

open ControlStack.SC06

/-- One confirmation of (agent 2, tool 7, value 42) authorizes two
sensitive effects in the existing full-check abstract machine. -/
theorem same_confirmation_can_authorize_two_effects :
    let s := run P0 full init [
      .writeTyped 1 0 42 99,
      .read 2 0,
      .confirm 5 3 2 7 42,
      .act 2 7 42 3,
      .act 2 7 42 3
    ]
    s.confs = [⟨3, 2, 7, 42, 5⟩] ∧
      s.executed = [⟨2, 7, 42, true, some 3⟩,
                    ⟨2, 7, 42, true, some 3⟩] := by
  decide

/-- The same trace without the trusted user confirmation has no effects.
Thus the finding is approval reuse, not an unapproved effect in SC06's sense. -/
theorem missing_confirmation_blocks_both :
    (run P0 full init [
      .writeTyped 1 0 42 99,
      .read 2 0,
      .act 2 7 42 3,
      .act 2 7 42 3
    ]).executed = [] := by
  decide

end ControlStack.SC06ConfirmationReuse

#print axioms ControlStack.SC06ConfirmationReuse.same_confirmation_can_authorize_two_effects
#print axioms ControlStack.SC06ConfirmationReuse.missing_confirmation_blocks_both
