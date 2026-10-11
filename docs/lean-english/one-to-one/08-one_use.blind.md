# Blind semantic target 8: ControlStack.Deployment.one_use

∀ R cap ops, ((run full R ops (initial cap)).reserved).Nodup

## English under test

`ControlStack.Deployment.one_use`  — `ControlStack/Deployment/Contracts.lean:155`
- **Says (plain English):** In the SC26 model with all checks on, after any finite sequence of operations at all (no legality premise), the list of reserved request ids contains no repeats. So each request id is reserved, and its amount is charged against the cap, at most once.
- **Under these hypotheses:** None beyond the model definition (the `execute` step refuses to reserve an id already in the reserved list when the nonce check is on, which it is in `full`). It holds for arbitrary roles, cap and operation list.

