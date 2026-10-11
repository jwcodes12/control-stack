# Blind semantic target 17: ControlStack.Deployment.indexed_receipts_sound

∀ R table start rs, verified table.step start rs = true → Trace R (table.interpret start) (table.interpret (recordedEnd start rs))

## English under test

`ControlStack.Deployment.indexed_receipts_sound`  — `ControlStack/Deployment/R2Contracts.lean:146`
- **Says (plain English):** Suppose a table assigns each of the abstract state ids a complete broker state (`interpret`), has a step function on ids, and every step of the table is a legal broker `Step` between the interpreted states (`checked`). Then if the replay checker `verified` accepts a list of receipts starting from id `start`, the interpreted states form a broker `Trace` from the start state to the interpreted last recorded state.
- **Under these hypotheses:** `IndexedBrokerTable R` is supplied: for every id and every operation, `Step R (interpret s) (interpret (step s op))` is a proof. That is checked in Lean for each concrete table, but it requires such a table to exist for the transcript. `verified table.step start rs = true`: each receipt's `before` is the running id and its `after` equals the table's step.

