import ControlStack.Scenarios.SC07Liveness
import ControlStack.Scenarios.SC07Exfil
#check ControlStack.SC07Exfil.windows_needed
#check ControlStack.SC07Exfil.sc07_mixed
#check ControlStack.SC07Exfil.sc07_fixed_budget
#check ControlStack.SC07Exfil.expected_leak_le
#check ControlStack.SC07Exfil.observable_schedule_exfil
#check ControlStack.SC07Exfil.datacenter_example
#print axioms ControlStack.SC07Exfil.windows_needed
#print axioms ControlStack.SC07Exfil.sc07_mixed
#print axioms ControlStack.SC07Exfil.sc07_fixed_budget
#print axioms ControlStack.SC07Exfil.expected_leak_le
#print axioms ControlStack.SC07Exfil.observable_schedule_exfil
#print axioms ControlStack.SC07Exfil.datacenter_example
#check ControlStack.SC07Liveness.sc07_safe
#print axioms ControlStack.SC07Liveness.sc07_safe
#check ControlStack.SC07Liveness.upload_completes
#print axioms ControlStack.SC07Liveness.upload_completes
#check ControlStack.SC07Liveness.exfil_needs_windows
#print axioms ControlStack.SC07Liveness.exfil_needs_windows
#check ControlStack.SC07Liveness.shared_quota_blocks
#print axioms ControlStack.SC07Liveness.shared_quota_blocks
