# Blind semantic target 11: ControlStack.Deployment.deployment_safe

∀ d r R cap ops sinkEffects actualEdges, Accepted d → ExtractionFaithful d r actualEdges → ProtocolRefinement d r R cap ops sinkEffects → exclusive actual sink ∧ authorized sinkEffects ∧ distinct keys ∧ total amount ≤ cap ∧ sinkEffects.length ≤ cap

## English under test

`ControlStack.Deployment.deployment_safe`  — `ControlStack/Deployment/Contracts.lean:192`
- **Says (plain English):** Suppose the IR is accepted, the extracted graph is faithful, and the real sink publications are linked to the SC26 model by a `ProtocolRefinement`. Then four things hold. (1) Every real authority edge into the sink comes from the receiver. (2) Every published sink effect `(key, payload)` has a request with exactly that payload, its key is reserved, and there is an approval of exactly that payload by someone in the approvers list who is not the requester. (3) The sink keys are all distinct. (4) The sum of published amounts is at most the cap, and the number of published effects is at most the cap.
- **Under these hypotheses:** `Accepted d` (the finite graph checks above). `ExtractionFaithful d r actualEdges`: every actual edge is in the IR, `r` is a node of the IR, and `r` is the receiver (a **world assumption**). `ProtocolRefinement d r R cap ops sinkEffects` has four fields, all **world assumptions** about the real system: (i) the model's gate credential equals the receiver's UID; (ii) every direct bank call in the model operation list carries the UID of some agent node; (iii) every published effect has amount exactly 1; (iv) the published sink effects are exactly equal (same list) to the bank ledger the model would produce when running `ops`. `ops` is a fixed list chosen by the theorem's caller.

