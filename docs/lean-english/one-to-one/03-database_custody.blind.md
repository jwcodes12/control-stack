# Blind semantic target 3: ControlStack.Deployment.database_custody

∀ d e, Accepted d → e ∈ d.edges → e.authority = true → e.target = d.database → e.source = d.receiver

## English under test

`ControlStack.Deployment.database_custody`  — `ControlStack/Deployment/Contracts.lean:118`
- **Says (plain English):** For an accepted deployment, any authority edge in the IR that targets the database has the receiver as its source.
- **Under these hypotheses:** `Accepted d`, plus the edge being in `d.edges`, marked authority, targeting `d.database`. Conditions on the model.

