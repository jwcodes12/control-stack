import ControlStack.Scenarios.AuthInstancesB
import ControlStack.Scenarios.SC12Persistence
#check ControlStack.SC12.sc12_safe
#check ControlStack.SC12.no_fire_after_end
#check ControlStack.SC12.halt_freezes
#check ControlStack.SC12.honest_session_lifecycle
#check ControlStack.SC12.registry_bypass_survives
#check ControlStack.SC12.parent_only_revocation_survives
#check ControlStack.SC12.foreign_registration_survives
#check ControlStack.SC12.no_halt_check_breaks
#print axioms ControlStack.SC12.sc12_safe
#print axioms ControlStack.SC12.no_fire_after_end
#print axioms ControlStack.SC12.halt_freezes
#print axioms ControlStack.SC12.honest_session_lifecycle
#print axioms ControlStack.SC12.registry_bypass_survives
#print axioms ControlStack.SC12.parent_only_revocation_survives
#print axioms ControlStack.SC12.foreign_registration_survives
#print axioms ControlStack.SC12.no_halt_check_breaks
#check ControlStack.AuthInstances.sc12_safe_authenticated
#print axioms ControlStack.AuthInstances.sc12_safe_authenticated
#check ControlStack.AuthInstances.forged12_spawns_without_auth
#print axioms ControlStack.AuthInstances.forged12_spawns_without_auth
