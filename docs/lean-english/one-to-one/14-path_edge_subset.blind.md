# Blind semantic target 14: ControlStack.Deployment.path_edge_subset

∀ d larger start target, edgeSubset d larger → sameBrokerReceiver d larger → AvoidedPath d start target → AvoidedPath larger start target

## English under test

`ControlStack.Deployment.path_edge_subset`  — `ControlStack/Deployment/R2Contracts.lean:27`
- **Says (plain English):** If every edge of `d` is also an edge of `larger`, and both have the same broker and receiver, then any avoided path in `d` from `start` to `target` is also an avoided path in `larger`.
- **Under these hypotheses:** Edge inclusion and equality of the broker and receiver ids. Conditions on the model.

