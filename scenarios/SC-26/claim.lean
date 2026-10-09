import ControlStack.Scenarios.SC26LossyLiveness
import ControlStack.Scenarios.SC26Liveness
import ControlStack.Core.AuthenticatedAdv
import ControlStack.Scenarios.SC26Authenticated
import ControlStack.Scenarios.SC26Transaction
import ControlStack.Scenarios.SC26Refinement
#check ControlStack.SC26.sc26_safe
#check ControlStack.SC26.safe_of_sound
#check ControlStack.SC26.good_without_nonce
#check ControlStack.SC26.sc26_safe_disjoint
#check ControlStack.SC26.sc26_once
#check ControlStack.SC26.halt_freezes
#check ControlStack.SC26.halt_freezes_quiescent
#check ControlStack.SC26.honest_trace_pays
#check ControlStack.SC26.inflight_after_halt
#check ControlStack.SC26.payload_unchecked_breaks
#check ControlStack.SC26.no_dedup_retry_duplicates
#check ControlStack.SC26.no_dedup_breaks_cap
#check ControlStack.SC26.no_cap_breaks
#check ControlStack.SC26.no_halt_check_breaks
#check ControlStack.SC26.no_bank_auth_breaks
#check ControlStack.SC26.gate_credential_leak_breaks
#check ControlStack.SC26.self_approval_without_distinct_check
#check ControlStack.SC26.nonce_protects_budget_only
#check ControlStack.SC26.same_payload_twice_is_good
#print axioms ControlStack.SC26.sc26_safe
#print axioms ControlStack.SC26.safe_of_sound
#print axioms ControlStack.SC26.good_without_nonce
#print axioms ControlStack.SC26.sc26_safe_disjoint
#print axioms ControlStack.SC26.sc26_once
#print axioms ControlStack.SC26.halt_freezes
#print axioms ControlStack.SC26.halt_freezes_quiescent
#print axioms ControlStack.SC26.honest_trace_pays
#print axioms ControlStack.SC26.inflight_after_halt
#print axioms ControlStack.SC26.payload_unchecked_breaks
#print axioms ControlStack.SC26.no_dedup_retry_duplicates
#print axioms ControlStack.SC26.no_dedup_breaks_cap
#print axioms ControlStack.SC26.no_cap_breaks
#print axioms ControlStack.SC26.no_halt_check_breaks
#print axioms ControlStack.SC26.no_bank_auth_breaks
#print axioms ControlStack.SC26.gate_credential_leak_breaks
#print axioms ControlStack.SC26.self_approval_without_distinct_check
#print axioms ControlStack.SC26.nonce_protects_budget_only
#print axioms ControlStack.SC26.same_payload_twice_is_good
#check ControlStack.SC26Refinement.simulation
#check ControlStack.SC26Refinement.concrete_safe
#check ControlStack.SC26Refinement.concrete_halt
#check ControlStack.SC26Refinement.recover_halt_witness
#print axioms ControlStack.SC26Refinement.simulation
#print axioms ControlStack.SC26Refinement.concrete_safe
#print axioms ControlStack.SC26Refinement.concrete_halt
#print axioms ControlStack.SC26Refinement.recover_halt_witness
#check ControlStack.SC26Authenticated.sc26_safe_authenticated
#print axioms ControlStack.SC26Authenticated.sc26_safe_authenticated
#check ControlStack.SC26Authenticated.forged_approval_pays_without_auth
#print axioms ControlStack.SC26Authenticated.forged_approval_pays_without_auth
#check ControlStack.AuthenticatedAdv.sc26_consent_from_honest_script
#print axioms ControlStack.AuthenticatedAdv.sc26_consent_from_honest_script
#check ControlStack.SC26Liveness.honest_progress
#print axioms ControlStack.SC26Liveness.honest_progress
#check ControlStack.SC26Liveness.progress_interleaved
#print axioms ControlStack.SC26Liveness.progress_interleaved
#check ControlStack.SC26Liveness.paid_once
#print axioms ControlStack.SC26Liveness.paid_once
#check ControlStack.SC26Liveness.halted_blocks
#print axioms ControlStack.SC26Liveness.halted_blocks
#check ControlStack.SC26Liveness.cap_exhausted_blocks
#print axioms ControlStack.SC26Liveness.cap_exhausted_blocks
#check ControlStack.SC26Liveness.Concrete.crash_tolerant_progress
#print axioms ControlStack.SC26Liveness.Concrete.crash_tolerant_progress
#check ControlStack.SC26Liveness.Concrete.crashes_forever_no_progress
#print axioms ControlStack.SC26Liveness.Concrete.crashes_forever_no_progress
#check ControlStack.SC26Liveness.Concrete.halted_concrete_no_progress
#print axioms ControlStack.SC26Liveness.Concrete.halted_concrete_no_progress
#check ControlStack.SC26LossyLiveness.lossy_safe
#print axioms ControlStack.SC26LossyLiveness.lossy_safe
#check ControlStack.SC26LossyLiveness.lossy_progress
#print axioms ControlStack.SC26LossyLiveness.lossy_progress
#check ControlStack.SC26LossyLiveness.lossy_rounds
#print axioms ControlStack.SC26LossyLiveness.lossy_rounds
#check ControlStack.SC26LossyLiveness.drop_all_no_progress
#print axioms ControlStack.SC26LossyLiveness.drop_all_no_progress
#check ControlStack.SC26LossyLiveness.no_dedup_lossy_pays_twice
#print axioms ControlStack.SC26LossyLiveness.no_dedup_lossy_pays_twice
