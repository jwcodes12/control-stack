import ControlStack.Scenarios.SC25Content
import ControlStack.Scenarios.SC25Audit
#check ControlStack.SC25.sc25_safe
#check ControlStack.SC25.step_expired
#check ControlStack.SC25.expired_never_executes
#check ControlStack.SC25.halt_freezes
#check ControlStack.SC25.honest_reversible
#check ControlStack.SC25.honest_irreversible_with_crash
#check ControlStack.SC25.audit_fail_blocks
#check ControlStack.SC25.fail_open_timeout_breaks
#check ControlStack.SC25.digest_unchecked_breaks
#check ControlStack.SC25.nonatomic_check_race_breaks
#check ControlStack.SC25.agent_declared_class_breaks
#check ControlStack.SC25.no_halt_check_breaks
#print axioms ControlStack.SC25.sc25_safe
#print axioms ControlStack.SC25.step_expired
#print axioms ControlStack.SC25.expired_never_executes
#print axioms ControlStack.SC25.halt_freezes
#print axioms ControlStack.SC25.honest_reversible
#print axioms ControlStack.SC25.honest_irreversible_with_crash
#print axioms ControlStack.SC25.audit_fail_blocks
#print axioms ControlStack.SC25.fail_open_timeout_breaks
#print axioms ControlStack.SC25.digest_unchecked_breaks
#print axioms ControlStack.SC25.nonatomic_check_race_breaks
#print axioms ControlStack.SC25.agent_declared_class_breaks
#print axioms ControlStack.SC25.no_halt_check_breaks
#check ControlStack.SC25Content.sc25_content_safe
#print axioms ControlStack.SC25Content.sc25_content_safe
#check ControlStack.SC25Content.digest_only_executes_unaudited
#print axioms ControlStack.SC25Content.digest_only_executes_unaudited
