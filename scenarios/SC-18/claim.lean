import ControlStack.Scenarios.SC18Refinement
import ControlStack.Scenarios.SC18Liveness
import ControlStack.Scenarios.AuthInstancesB
import ControlStack.Scenarios.SC18Logging
#check ControlStack.SC18.sc18_safe
#check ControlStack.SC18.config_untampered
#check ControlStack.SC18.halt_freezes
#check ControlStack.SC18.honest_logged_release
#check ControlStack.SC18.release_before_log_breaks
#check ControlStack.SC18.agent_writable_config_breaks
#check ControlStack.SC18.fail_open_outage_breaks
#check ControlStack.SC18.watchdog_off_silent_release
#check ControlStack.SC18.no_halt_check_breaks
#print axioms ControlStack.SC18.sc18_safe
#print axioms ControlStack.SC18.config_untampered
#print axioms ControlStack.SC18.halt_freezes
#print axioms ControlStack.SC18.honest_logged_release
#print axioms ControlStack.SC18.release_before_log_breaks
#print axioms ControlStack.SC18.agent_writable_config_breaks
#print axioms ControlStack.SC18.fail_open_outage_breaks
#print axioms ControlStack.SC18.watchdog_off_silent_release
#print axioms ControlStack.SC18.no_halt_check_breaks
#check ControlStack.AuthInstances.sc18_safe_authenticated
#print axioms ControlStack.AuthInstances.sc18_safe_authenticated
#check ControlStack.AuthInstances.forged18_redirects_without_auth
#print axioms ControlStack.AuthInstances.forged18_redirects_without_auth
#check ControlStack.SC18Liveness.honest_release
#print axioms ControlStack.SC18Liveness.honest_release
#check ControlStack.SC18Liveness.progress_interleaved
#print axioms ControlStack.SC18Liveness.progress_interleaved
#check ControlStack.SC18Liveness.silent_ticks_halt
#print axioms ControlStack.SC18Liveness.silent_ticks_halt
#check ControlStack.SC18Liveness.Resume.resume_safe
#print axioms ControlStack.SC18Liveness.Resume.resume_safe
#check ControlStack.SC18Liveness.Resume.resume_progress
#print axioms ControlStack.SC18Liveness.Resume.resume_progress
#check ControlStack.SC18Refinement.simulation
#print axioms ControlStack.SC18Refinement.simulation
#check ControlStack.SC18Refinement.concrete_safe
#print axioms ControlStack.SC18Refinement.concrete_safe
#check ControlStack.SC18Refinement.concrete_durable
#print axioms ControlStack.SC18Refinement.concrete_durable
#check ControlStack.SC18Refinement.honest_path
#print axioms ControlStack.SC18Refinement.honest_path
#check ControlStack.SC18Refinement.fail_open_breaks
#print axioms ControlStack.SC18Refinement.fail_open_breaks
#check ControlStack.SC18Refinement.late_reply_breaks_timing
#print axioms ControlStack.SC18Refinement.late_reply_breaks_timing
