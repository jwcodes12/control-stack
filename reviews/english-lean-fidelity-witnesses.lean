/-!
Isolated source-fidelity countermodels / nonvacuity witnesses.
This file changes no theorem or implementation. The source commit under audit is
bda1a50b8ef75bf0c79f3440a43f426f79cb4901.

IMPORTANT: This file has NOT been independently kernel-checked by this audit
environment. Run with the repository's pinned Lean 4.34.0:
  lake env lean reviews/english-lean-fidelity-witnesses.lean

The two theorems only show executions are accepted for a caller-free operation
alphabet; they DO NOT assert a counterexample to either Lean safety theorem.
To represent a *different physical caller* requires a richer transition system.
-/
import ControlStack.GateClients
import ControlStack.Lease

namespace ControlStack.FidelityWitnesses

private def tx : GateClients.Approval.Tx Unit :=
  { payload := (), nonce := 7, expiry := 0 }

/-- An approval plus execute operation commits a transaction. No caller or
executor identity is supplied to execute; the transition system cannot tell
whether the invoking process is the intended actor. -/
theorem approval_without_executor_identity :
    let init : GateClients.Approval.St Unit := ⟨0, [], [], []⟩
    let operations : List (GateClients.Approval.Op Unit) :=
      [.approve tx, .execute tx]
    (operations.foldl GateClients.Approval.step init).executed = [(tx, 0)] := by
  decide

/-- The transition accepts work charged to worker 1 solely because the
operation names worker 1. There is no authenticated caller argument in Op.work.
A separate identity/refinement model is needed to rule out impersonation. -/
theorem work_charged_by_worker_name_only :
    let operations : List Lease.Op := [.issue ⟨17, 1, 0⟩ 1, .work 1 1]
    (operations.foldl (Lease.step 1) Lease.init).work = [(17, 1, 0)] := by
  decide

#print axioms approval_without_executor_identity
#print axioms work_charged_by_worker_name_only

end ControlStack.FidelityWitnesses
