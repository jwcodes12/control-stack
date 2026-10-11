# Blind semantic target 15: ControlStack.Deployment.requested_monotonicity_counterexample

sinkOnly.nodes = clean.nodes ∧ edgesSubset sinkOnly clean ∧ receiverSinkWritePresent sinkOnly ∧ Accepted clean ∧ ¬ Accepted sinkOnly

## English under test

`ControlStack.Deployment.requested_monotonicity_counterexample`  — `ControlStack/Deployment/R2Contracts.lean:53`
- **Says (plain English):** A concrete finite check. The IR `sinkOnly` has the same nodes as `clean`; every edge of `sinkOnly` is an edge of `clean`; it still contains the receiver's write edge into the sink; `clean` is accepted; but `sinkOnly` is not accepted. So "Accepted" is not preserved when edges are removed (it also demands that the broker and receiver database-write edges be present).
- **Under these hypotheses:** None (closed statement about two named IRs).

