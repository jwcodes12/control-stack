import ControlStack.Scenarios.SC28Refinement
import ControlStack.Core.AntiRollback
import ControlStack.Scenarios.SC28Liveness
import ControlStack.Scenarios.AuthInstancesA
import ControlStack.Scenarios.SC28Budget
#check ControlStack.SC28.sc28_safe
#check ControlStack.SC28.revoked_lease_stops
#check ControlStack.SC28.fork_shares_lease
#check ControlStack.SC28.halt_freezes
#check ControlStack.SC28.honest_trace_works
#check ControlStack.SC28.no_global_counter_breaks
#check ControlStack.SC28.fresh_fork_exceeds_parent
#check ControlStack.SC28.fresh_fork_escapes_revocation
#check ControlStack.SC28.reported_cost_breaks
#check ControlStack.SC28.rollback_double_spends
#check ControlStack.SC28.no_halt_check_breaks
#print axioms ControlStack.SC28.sc28_safe
#print axioms ControlStack.SC28.revoked_lease_stops
#print axioms ControlStack.SC28.fork_shares_lease
#print axioms ControlStack.SC28.halt_freezes
#print axioms ControlStack.SC28.honest_trace_works
#print axioms ControlStack.SC28.no_global_counter_breaks
#print axioms ControlStack.SC28.fresh_fork_exceeds_parent
#print axioms ControlStack.SC28.fresh_fork_escapes_revocation
#print axioms ControlStack.SC28.reported_cost_breaks
#print axioms ControlStack.SC28.rollback_double_spends
#print axioms ControlStack.SC28.no_halt_check_breaks
#check ControlStack.AuthInstances.sc28_safe_authenticated
#print axioms ControlStack.AuthInstances.sc28_safe_authenticated
#check ControlStack.AuthInstances.forged28_consumes_without_auth
#print axioms ControlStack.AuthInstances.forged28_consumes_without_auth
#check ControlStack.SC28Liveness.honest_steps_progress
#print axioms ControlStack.SC28Liveness.honest_steps_progress
#check ControlStack.SC28Liveness.progress_interleaved
#print axioms ControlStack.SC28Liveness.progress_interleaved
#check ControlStack.SC28Liveness.global_cap_blocks_honest
#print axioms ControlStack.SC28Liveness.global_cap_blocks_honest
#check ControlStack.AntiRollback.rollback_transfer
#print axioms ControlStack.AntiRollback.rollback_transfer
#check ControlStack.AntiRollback.sc28_rollback_safe
#print axioms ControlStack.AntiRollback.sc28_rollback_safe
#check ControlStack.SC28Refinement.simulation
#print axioms ControlStack.SC28Refinement.simulation
#check ControlStack.SC28Refinement.concrete_safe
#print axioms ControlStack.SC28Refinement.concrete_safe
#check ControlStack.SC28Refinement.concrete_counters_safe
#print axioms ControlStack.SC28Refinement.concrete_counters_safe
#check ControlStack.SC28Refinement.concrete_revoked_stops
#print axioms ControlStack.SC28Refinement.concrete_revoked_stops
#check ControlStack.SC28Refinement.exclusive_placement_safe
#print axioms ControlStack.SC28Refinement.exclusive_placement_safe
#check ControlStack.SC28Refinement.unplaced_invisible
#print axioms ControlStack.SC28Refinement.unplaced_invisible
