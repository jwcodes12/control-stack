import ControlStack

/-!
  Source-SHA 083874048518b68d754f0c392ad0cb84f01174ba.
  Inspect the actual elaborated declarations: source-normalized catalogues are not enough.
  Only Lean's output below is evidence of elaborated types and axioms.
-/
set_option pp.explicit true
set_option pp.universes true
set_option pp.maxDepth 75
set_option pp.maxSteps 150000
#print ControlStack.Gate.Spec
#print ControlStack.Gate.Spec.trace_safe
#print axioms ControlStack.Gate.Spec.trace_safe
#print ControlStack.Gate.withHalt_spec
#print axioms ControlStack.Gate.withHalt_spec
#print ControlStack.HaltLiveness.DeliveredWithin
#print ControlStack.HaltLiveness.liveness_if_delivered
#print axioms ControlStack.HaltLiveness.liveness_if_delivered
#print ControlStack.GatewayCore.core_bound
#print axioms ControlStack.GatewayCore.core_bound
#print ControlStack.GatewayCore.finalView
#print ControlStack.GatewayCore.refusal_blanks
#print ControlStack.GatewayCore.close_freezes
#print ControlStack.SafetyCaseSC01.sc01_case
#print axioms ControlStack.SafetyCaseSC01.sc01_case
#print ControlStack.Leakage.covert_seq_seed
#print axioms ControlStack.Leakage.covert_seq_seed
#print ControlStack.Leakage.survInd
#print ControlStack.Leakage.audit_leak_bound
#print axioms ControlStack.Leakage.audit_leak_bound
#print ControlStack.GateClients.Artifact.deployed_is_reviewed
#print axioms ControlStack.GateClients.Artifact.deployed_is_reviewed
#print ControlStack.GateClients.Approval.approval_safe
#print axioms ControlStack.GateClients.Approval.approval_safe
#print ControlStack.Lease.lease_safe
#print ControlStack.Lease.revoke_absorbing
#print ControlStack.PolicyTamper.policy_preserved_if_protected
#print ControlStack.GateComposition.shared_invariants
#print axioms ControlStack.GateComposition.shared_invariants
#print ControlStack.Compose.jointView
#print ControlStack.Compose.joint_pass_prob
#print ControlStack.Compose.composedEndToEnd
#print axioms ControlStack.Compose.composedEndToEnd
#print ControlStack.ComposeAvg.composedPop_end
#print ControlStack.ComposeCoverage.composedCov_end
