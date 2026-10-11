# Blind semantic target 25: ControlStack.Deployment.TranscriptReplay.replay_was_not_allowed

∀ now a' l', ¬ Allowed s8 now q8 a' l'

## English under test

`ControlStack.Deployment.TranscriptReplay.replay_was_not_allowed`  — `ControlStack/Deployment/TranscriptReplay.lean:125`
- **Says (plain English):** In the model state `s8` reached just after the first release (nonce 1), the request `q8` (which has the same fields as the first release's request, so the same nonce) fails the release guard, whatever clock value, approval record and lease are offered. That is the model's explanation of the recorded denial in step 8.
- **Under these hypotheses:** None beyond the definitions; it quantifies over every clock value `now`, approval `a'` and lease `l'`.

