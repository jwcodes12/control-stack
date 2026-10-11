# Blind semantic target 9: ControlStack.Deployment.gate_contract

∀ R cap legalOps, invariant finalState ∧ initialEffects.IsPrefix finalEffects ∧ ∀ effect ∈ finalEffects, acceptable effect

## English under test

`ControlStack.Deployment.gate_contract`  — `ControlStack/Deployment/Contracts.lean:159`
- **Says (plain English):** Treat the SC26 model as an instance of the generic "gate" interface, where each step is an operation together with a proof that it is legal. Then after running any list of legal operations from the initial state: the SC26 invariant holds; the initial effect log (the bank) is a prefix of the final one (so the bank is append-only); and every bank entry is acceptable (has a request with that payload, is reserved, is approved by a non-requesting approver).
- **Under these hypotheses:** Operations are subtyped by `legal`, so each is individually legal. The model is `SC26.full`.

