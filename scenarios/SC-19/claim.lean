import ControlStack.Scenarios.AuthInstancesA
import ControlStack.Scenarios.SC19Prod
#check ControlStack.SC19.sc19_safe
#check ControlStack.SC19.halt_freezes
#check ControlStack.SC19.honest_destructive_change
#check ControlStack.SC19.stale_snapshot_breaks
#check ControlStack.SC19.unverified_snapshot_breaks
#check ControlStack.SC19.blast_radius_race_breaks
#check ControlStack.SC19.no_halt_check_breaks
#print axioms ControlStack.SC19.sc19_safe
#print axioms ControlStack.SC19.halt_freezes
#print axioms ControlStack.SC19.honest_destructive_change
#print axioms ControlStack.SC19.stale_snapshot_breaks
#print axioms ControlStack.SC19.unverified_snapshot_breaks
#print axioms ControlStack.SC19.blast_radius_race_breaks
#print axioms ControlStack.SC19.no_halt_check_breaks
#check ControlStack.AuthInstances.sc19_safe_authenticated
#print axioms ControlStack.AuthInstances.sc19_safe_authenticated
#check ControlStack.AuthInstances.forged19_destroys_without_auth
#print axioms ControlStack.AuthInstances.forged19_destroys_without_auth
