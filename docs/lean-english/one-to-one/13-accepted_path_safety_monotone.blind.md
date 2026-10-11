# Blind semantic target 13: ControlStack.Deployment.accepted_path_safety_monotone

∀ d larger, edgeSubset d larger → sameNodesAndFourIds d larger → Accepted larger → ∀ a ∈ d.nodes, a.agent = true → ¬ AvoidedPath d a.id d.sink ∧ ¬ AvoidedPath d a.id d.database

## English under test

`ControlStack.Deployment.accepted_path_safety_monotone`  — `ControlStack/Deployment/R2Contracts.lean:38`
- **Says (plain English):** If a larger IR is accepted, and a smaller IR `d` has the same nodes, same broker/receiver/sink/database ids and only a subset of the edges, then for every agent node of `d` there is no avoided path to the sink or the database in `d`. So dropping edges from an accepted graph cannot create a bypass path.
- **Under these hypotheses:** Edge-subset inclusion; equality of node lists and of the four distinguished ids; `Accepted larger`. Conditions on the model.

