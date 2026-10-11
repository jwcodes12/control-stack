# Blind semantic target 23: ControlStack.Deployment.TranscriptReplay.runtime_trace

Trace roles (initial 2) s10; additionally ten specified transitions if the prose order is treated as part of the claim

## English under test

`ControlStack.Deployment.TranscriptReplay.runtime_trace`  — `ControlStack/Deployment/TranscriptReplay.lean:108`
- **Says (plain English):** There is a chain of ten broker model steps from the initial state with cap 2 to the specific state `s10`. The ten steps are, in order: stage artifact 1; review it; issue lease 1; approve nonce 1; stage by the second agent; issue lease 2; approve nonce 2; release nonce 1; a denial; release nonce 2.
- **Under these hypotheses:** None as a statement. The proof builds the ten steps by hand (each by `ok`/`decide`) and shows the receipt list passes the replay checker. What it means for the real run depends on a premise that is not proved: that the recorded request/response log (hash cited in the file header) is genuine, complete, in the real order, and that each recorded response corresponds to the model step it was mapped to.

