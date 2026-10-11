# Blind semantic target 10: ControlStack.Deployment.broker_contract

∀ R cap t, Trace R (initial cap) t → Safe t

## English under test

`ControlStack.Deployment.broker_contract`  — `ControlStack/Deployment/Contracts.lean:168`
- **Says (plain English):** In the SQLite-broker transition model (`TrustedBroker`), any state `t` reachable from the initial state with cap `cap` by any sequence of model steps is "Safe". Safe means four things: total spent is at most the cap; the number of releases is at most the amount spent; the list of consumed nonces has no repeats; and every lease's used amount is at most its budget.
- **Under these hypotheses:** `Trace R (initial cap) t`, a finite chain of `Step`s. Each step is one of: deny (no-op); stage an artifact (agent role); review (reviewer role, artifact exists); issue a lease (admin role); approve (approver role, matching review by a different reviewer, lease active, unexpired); revoke (admin); release (the `Allowed` guard); halt (admin). The `Roles` record carries a field `separated` saying no agent uid is a reviewer, approver or admin uid. That field is a **world assumption** supplied by whoever builds `R`. Time `now` is an arbitrary input (the docstring says no anti-rollback guarantee is inferred).

