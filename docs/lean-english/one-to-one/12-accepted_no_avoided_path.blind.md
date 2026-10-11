# Blind semantic target 12: ControlStack.Deployment.accepted_no_avoided_path

∀ d a target, Accepted d → a ∈ d.nodes → a.agent = true → target ≠ a.id → ¬ AvoidedPath d a.id target

## English under test

`ControlStack.Deployment.accepted_no_avoided_path`  — `ControlStack/Deployment/R2Contracts.lean:20`
- **Says (plain English):** For an accepted deployment, no agent node can reach any node other than itself by a path that avoids the broker and receiver.
- **Under these hypotheses:** `Accepted d` and `a` an agent node of the IR. Conditions on the model; the IR containing every real edge is the **world assumption** (`faithful_extraction`).

