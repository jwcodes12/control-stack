import ControlStack.Scenarios.SC23IsolationV2
import ControlStack.Scenarios.SC23Isolation
import ControlStack.Scenarios.SC23Injection
#check ControlStack.SC23.sc23_safe
#check ControlStack.SC23.halt_freezes
#check ControlStack.SC23.honest_untainted
#check ControlStack.SC23.honest_confirmed
#check ControlStack.SC23.tainted_unconfirmed_blocked
#check ControlStack.SC23.summarizer_drops_taint
#check ControlStack.SC23.paraphrase_confirmation_breaks
#check ControlStack.SC23.no_taint_check_breaks
#check ControlStack.SC23.confirmation_reuse_breaks
#check ControlStack.SC23.non_user_confirmation_refused
#print axioms ControlStack.SC23.sc23_safe
#print axioms ControlStack.SC23.halt_freezes
#print axioms ControlStack.SC23.honest_untainted
#print axioms ControlStack.SC23.honest_confirmed
#print axioms ControlStack.SC23.tainted_unconfirmed_blocked
#print axioms ControlStack.SC23.summarizer_drops_taint
#print axioms ControlStack.SC23.paraphrase_confirmation_breaks
#print axioms ControlStack.SC23.no_taint_check_breaks
#print axioms ControlStack.SC23.confirmation_reuse_breaks
#print axioms ControlStack.SC23.non_user_confirmation_refused
#check ControlStack.SC23Isolation.noninterference
#print axioms ControlStack.SC23Isolation.noninterference
#check ControlStack.SC23Isolation.w1_impossible
#print axioms ControlStack.SC23Isolation.w1_impossible
#check ControlStack.SC23Isolation.sc23_isolated_safe
#print axioms ControlStack.SC23Isolation.sc23_isolated_safe
#check ControlStack.SC23IsolationV2.noninterference_authed
#print axioms ControlStack.SC23IsolationV2.noninterference_authed
#check ControlStack.SC23IsolationV2.w1_impossible_v2
#print axioms ControlStack.SC23IsolationV2.w1_impossible_v2
#check ControlStack.SC23IsolationV2.sc23v2_safe_authenticated
#print axioms ControlStack.SC23IsolationV2.sc23v2_safe_authenticated
