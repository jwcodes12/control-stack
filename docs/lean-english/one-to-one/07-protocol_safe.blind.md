# Blind semantic target 7: ControlStack.Deployment.protocol_safe

∀ R cap ops, (∀ op ∈ ops, legal R op) → Authorized R (run full R ops (initial cap)) ∧ distinct bank keys ∧ total bank amounts ≤ cap

## English under test

`ControlStack.Deployment.protocol_safe`  — `ControlStack/Deployment/Contracts.lean:151`
- **Says (plain English):** In the SC26 gate-and-bank model, start from the empty state and run any finite sequence of operations (requests, approvals, executions, delivery retries, message arrivals, direct bank calls, halts), as long as no direct bank call carries the gate's credential. Then in the final state: (1) every entry in the bank has a stored request with exactly that payload, the request id has been reserved, and there is an approval of exactly that payload by someone in the approvers list who is not the requester; (2) bank keys are all distinct; (3) the sum of the bank entries' amounts is at most the cap.
- **Under these hypotheses:** Every operation in the list is `legal` (the only restriction is that a `bankCall` is not made with the gate's credential; all other operations are unrestricted). The model's checks are all enabled (`SC26.full`): approval distinctness, payload-exact approval, nonce guard, cap guard, halt check, bank deduplication, bank authentication. The roles record `R` (agents, approvers, admins, gate credential) and `cap` are arbitrary.

