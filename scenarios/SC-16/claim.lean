import ControlStack.Scenarios.SC16Refinement
import ControlStack.Scenarios.AuthInstancesA
import ControlStack.Scenarios.SC16Disjoint
import ControlStack.Scenarios.SC16Deploy
#check ControlStack.SC16.sc16_safe
#check ControlStack.SC16.sc16_reviewed_content
#check ControlStack.SC16.halt_freezes
#check ControlStack.SC16.honest_trace_deploys
#check ControlStack.SC16.toctou_slot_breaks
#check ControlStack.SC16.collision_breaks
#check ControlStack.SC16.no_target_binding_breaks
#check ControlStack.SC16.no_nonce_redeploys
#check ControlStack.SC16.no_halt_check_breaks
#print axioms ControlStack.SC16.sc16_safe
#print axioms ControlStack.SC16.sc16_reviewed_content
#print axioms ControlStack.SC16.halt_freezes
#print axioms ControlStack.SC16.honest_trace_deploys
#print axioms ControlStack.SC16.toctou_slot_breaks
#print axioms ControlStack.SC16.collision_breaks
#print axioms ControlStack.SC16.no_target_binding_breaks
#print axioms ControlStack.SC16.no_nonce_redeploys
#print axioms ControlStack.SC16.no_halt_check_breaks
#check ControlStack.SC16Disjoint.sc16_safe_disjoint
#print axioms ControlStack.SC16Disjoint.sc16_safe_disjoint
#check ControlStack.SC16Disjoint.overlap_reviewer_is_agent
#print axioms ControlStack.SC16Disjoint.overlap_reviewer_is_agent
#check ControlStack.AuthInstances.sc16_safe_authenticated
#print axioms ControlStack.AuthInstances.sc16_safe_authenticated
#check ControlStack.AuthInstances.forged16_deploys_without_auth
#print axioms ControlStack.AuthInstances.forged16_deploys_without_auth
#check ControlStack.SC16Refinement.simulation
#print axioms ControlStack.SC16Refinement.simulation
#check ControlStack.SC16Refinement.concrete_safe
#print axioms ControlStack.SC16Refinement.concrete_safe
#check ControlStack.SC16Refinement.concrete_reviewed_content
#print axioms ControlStack.SC16Refinement.concrete_reviewed_content
#check ControlStack.SC16Refinement.concrete_safe_disjoint
#print axioms ControlStack.SC16Refinement.concrete_safe_disjoint
#check ControlStack.SC16Refinement.by_tag_breaks
#print axioms ControlStack.SC16Refinement.by_tag_breaks
