# Blind semantic target 20: ControlStack.TrustedBroker.halted_absorbing

∀ R s t, s.halted = true → Step R s t → t = s

## English under test

`ControlStack.TrustedBroker.halted_absorbing`  — `ControlStack/TrustedBroker.lean:196`
- **Says (plain English):** If the broker model's state is halted, then any single step from it leaves the entire state unchanged.
- **Under these hypotheses:** `s.halted = true` and `Step roles s t`. The proof relies on every constructor except `deny` and `halt` requiring `halted = false` (including `release` via `Allowed`).

