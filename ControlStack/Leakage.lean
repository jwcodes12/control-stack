import ControlStack.Core.Leakage

/-! Backward-compatible module import. Definitions live in `ControlStack/Core/Leakage.lean`.
Historical source receipts and PREREG files have not been modified. -/

/-! Historic SC-01 assurance theorem queries at the original module path. -/
#print axioms ControlStack.Leakage.transfer
#print axioms ControlStack.Leakage.covert_from_transfer
#print axioms ControlStack.Leakage.seq_transfer
#print axioms ControlStack.Leakage.seq_transfer_const
#print axioms ControlStack.Leakage.mass_le_prod
#print axioms ControlStack.Leakage.mass_const
#print axioms ControlStack.Leakage.covert_seq
#print axioms ControlStack.Leakage.episode_dom
#print axioms ControlStack.Leakage.sc01_adaptive_target
#print axioms ControlStack.Leakage.cval_live
#print axioms ControlStack.Leakage.blind_audit
#print axioms ControlStack.Leakage.audit_leak_bound
#print axioms ControlStack.Leakage.audit_leak_prod
#print axioms ControlStack.Leakage.audit_adaptive_hidden
