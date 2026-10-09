import ControlStack.Scenarios.SC17Drift
import ControlStack.Scenarios.SC17Infra
#check ControlStack.SC17.sc17_safe
#check ControlStack.SC17.reconcile_restores
#check ControlStack.SC17.halt_freezes
#check ControlStack.SC17.honest_apply
#check ControlStack.SC17.text_ceiling_composition_breaks
#check ControlStack.SC17.approve_then_amend_breaks
#check ControlStack.SC17.no_drift_detection_breaks
#check ControlStack.SC17.no_halt_check_breaks
#print axioms ControlStack.SC17.sc17_safe
#print axioms ControlStack.SC17.reconcile_restores
#print axioms ControlStack.SC17.halt_freezes
#print axioms ControlStack.SC17.honest_apply
#print axioms ControlStack.SC17.text_ceiling_composition_breaks
#print axioms ControlStack.SC17.approve_then_amend_breaks
#print axioms ControlStack.SC17.no_drift_detection_breaks
#print axioms ControlStack.SC17.no_halt_check_breaks
#check ControlStack.SC17Drift.drift_bounded
#print axioms ControlStack.SC17Drift.drift_bounded
#check ControlStack.SC17Drift.drift_lifetime
#print axioms ControlStack.SC17Drift.drift_lifetime
