# Blind semantic target 26: ControlStack.Deployment.TranscriptReplay.omitted_tail_is_accepted

verified table.step start (receipts.take 9) = true

## English under test

`ControlStack.Deployment.TranscriptReplay.omitted_tail_is_accepted`  — `ControlStack/Deployment/TranscriptReplay.lean:137`
- **Says (plain English):** The replay checker also accepts the transcript with its last receipt (the second release) removed: the first nine receipts form a valid shorter chain. A companion theorem (not translated here) says the end state then differs from the full one.
- **Under these hypotheses:** None (a closed finite computation by `decide`).

