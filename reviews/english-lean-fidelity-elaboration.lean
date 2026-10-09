import ControlStack

/-!
Read-only *elaborated* statement/axiom harness, not a proof of runtime correspondence.
Run on the pinned toolchain after `lake build ControlStack`:
  lake env lean reviews/english-lean-fidelity-elaboration.lean
The recorded definitions below are printed by the Lean elaborator on the
actual repository source, not transcribed from the normalized catalog.
-/
set_option pp.explicit true
set_option pp.universes true

#check ControlStack.Gate.Spec.trace_safe
#print ControlStack.Gate.Spec.trace_safe
#print axioms ControlStack.Gate.Spec.trace_safe

#check ControlStack.Gate.withHalt_spec
#print ControlStack.Gate.withHalt_spec
#print axioms ControlStack.Gate.withHalt_spec

#check ControlStack.Gate.halt_absorbing
#print ControlStack.Gate.halt_absorbing
#print axioms ControlStack.Gate.halt_absorbing

#check ControlStack.GatewayCore.core_bound
#print ControlStack.GatewayCore.core_bound
#print axioms ControlStack.GatewayCore.core_bound

#check ControlStack.GatewayCore.refusal_blanks
#print ControlStack.GatewayCore.refusal_blanks
#print axioms ControlStack.GatewayCore.refusal_blanks

#check ControlStack.GatewayCore.close_freezes
#print ControlStack.GatewayCore.close_freezes
#print axioms ControlStack.GatewayCore.close_freezes

#check ControlStack.SafetyCaseSC01.sc01_case
#print ControlStack.SafetyCaseSC01.sc01_case
#print axioms ControlStack.SafetyCaseSC01.sc01_case

#check ControlStack.Leakage.covert_seq_seed
#print ControlStack.Leakage.covert_seq_seed
#print axioms ControlStack.Leakage.covert_seq_seed

#check ControlStack.Leakage.audit_leak_bound
#print ControlStack.Leakage.audit_leak_bound
#print axioms ControlStack.Leakage.audit_leak_bound

#check ControlStack.HaltLiveness.liveness_if_delivered
#print ControlStack.HaltLiveness.liveness_if_delivered
#print axioms ControlStack.HaltLiveness.liveness_if_delivered

#check ControlStack.GateClients.Artifact.deployed_is_reviewed
#print ControlStack.GateClients.Artifact.deployed_is_reviewed
#print axioms ControlStack.GateClients.Artifact.deployed_is_reviewed

#check ControlStack.GateClients.Approval.approval_safe
#print ControlStack.GateClients.Approval.approval_safe
#print axioms ControlStack.GateClients.Approval.approval_safe

#check ControlStack.Lease.lease_safe
#print ControlStack.Lease.lease_safe
#print axioms ControlStack.Lease.lease_safe

#check ControlStack.Lease.revoke_absorbing
#print ControlStack.Lease.revoke_absorbing
#print axioms ControlStack.Lease.revoke_absorbing

#check ControlStack.PolicyTamper.policy_preserved_if_protected
#print ControlStack.PolicyTamper.policy_preserved_if_protected
#print axioms ControlStack.PolicyTamper.policy_preserved_if_protected

#check ControlStack.GateComposition.shared_invariants
#print ControlStack.GateComposition.shared_invariants
#print axioms ControlStack.GateComposition.shared_invariants

#check ControlStack.Compose.composedEndToEnd
#print ControlStack.Compose.composedEndToEnd
#print axioms ControlStack.Compose.composedEndToEnd

#check ControlStack.ComposeAvg.composedPop_end
#print ControlStack.ComposeAvg.composedPop_end
#print axioms ControlStack.ComposeAvg.composedPop_end

#check ControlStack.ComposeCoverage.composedCov_end
#print ControlStack.ComposeCoverage.composedCov_end
#print axioms ControlStack.ComposeCoverage.composedCov_end
