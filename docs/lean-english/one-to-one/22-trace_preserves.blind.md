# Blind semantic target 22: ControlStack.TrustedBroker.trace_preserves

∀ R s t, Safe s → Trace R s t → Safe t

## English under test

`ControlStack.TrustedBroker.trace_preserves`  — `ControlStack/TrustedBroker.lean:233`
- **Says (plain English):** If a state `s` is Safe and `t` is reachable from `s` by any finite sequence of model steps, then `t` is Safe.
- **Under these hypotheses:** `Safe s` and `Trace roles s t`.

