# Blind semantic target 24: ControlStack.Deployment.TranscriptReplay.final_safe

Safe s10

## English under test

`ControlStack.Deployment.TranscriptReplay.final_safe`  — `ControlStack/Deployment/TranscriptReplay.lean:113`
- **Says (plain English):** The final model state `s10` of the replayed transcript is Safe: spent (2) is at most cap (2); releases at most spent; consumed nonces distinct; every lease within budget.
- **Under these hypotheses:** None as a statement; it follows from `runtime_trace` plus `trace_preserves`. The same caveats as `runtime_trace` about whether the recorded log is the true run apply.

