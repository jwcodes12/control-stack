# English statements under test

### Claim 1
## `ControlStack.Deployment.indexed_receipts_sound`

- **Says (plain English):** Suppose a table assigns each of the abstract state ids a complete broker state (`interpret`), has a step function on ids, and every step of the table is a legal broker `Step` between the interpreted states (`checked`). Then if the replay checker `verified` accepts a list of receipts starting from id `start`, the interpreted states form a broker `Trace` from the start state to the interpreted last recorded state.
- **Under these hypotheses:** `IndexedBrokerTable R` is supplied: for every id and every operation, `Step R (interpret s) (interpret (step s op))` is a proof. That is checked in Lean for each concrete table, but it requires such a table to exist for the transcript. `verified table.step start rs = true`: each receipt's `before` is the running id and its `after` equals the table's step.
- **Does NOT say:** (a) It does not say the receipts are real, complete or in the order the broker actually ran them. (b) It says nothing about the sink. (c) A shorter list also passes (see `omitted_tail_is_accepted`).
- **Kind:** `general theorem` (an induction over the receipt list).

### Claim 2
## `ControlStack.TrustedBroker.transaction_preserves`

- **Says (plain English):** If a broker state `s` is Safe (spent at most cap; releases at most spent; consumed nonces distinct; every lease used at most its budget) and `t` is obtained from `s` by one model step, then `t` is Safe.
- **Under these hypotheses:** `Safe s` and `Step roles s t`. The step guards (role checks, `Allowed` for release, lease validity on issue) are conditions of the model; they are the content of the proof. The proof for release uses that `Allowed` demands a positive cost, `used + cost <= budget`, `spent + cost <= cap` and that the nonce is not in the consumed list.
- **Does NOT say:** (a) Safe does not mention approvals, reviews, digests or destinations. (b) It does not cover any real transition that is not a `Step` (the model has no step that falsifies the `intact` flag, so tampering of staged bytes is outside it). (c) Time is an unconstrained input, so no clock-rollback protection follows.
- **Kind:** `general theorem` (one-step case analysis on the `Step` constructors).

### Claim 3
## `ControlStack.TrustedBroker.transaction_coherent`

- **Says (plain English):** Call a broker state "coherent" when a nonce is in the consumed-history list exactly when the approval stored under that nonce exists and is marked used. A single model step preserves coherence.
- **Under these hypotheses:** `Coherent s` and `Step roles s t`. For the approve step the proof uses that the nonce was fresh and the new approval is unused; for release both the history and the flag are updated together.
- **Does NOT say:** It does not say the real database's `used` column and any log agree; it is only about the two fields of the model state. It is a supporting invariant (it is what lets the main theorem turn "nonce is in consumed" into "approval is used").
- **Kind:** `general theorem` (one-step case analysis).

### Claim 4
## `ControlStack.TrustedBroker.committed_nonce_unusable`

- **Says (plain English):** For any state `s` and any release `(r, a, l)`, after applying the release (the function `committed`), no request `r'` with the same nonce as `r` can satisfy the release guard `Allowed`, whatever approval, lease or clock value is offered.
- **Under these hypotheses:** None beyond `r'.nonce = r.nonce`. The statement does not require that the release itself was Allowed in `s`. The proof uses the fact that `committed` stores the approval under the nonce with `used = true`, while `Allowed` requires the approval to have `used = false`.
- **Does NOT say:** (a) A different nonce for the same digest can be approved and released again (limited only by lease and global budget). (b) It is not about the sink; one nonce yields at most one broker release, not "one file". (c) It depends on the guard reading the stored `used` flag; whether the real SQL does so is part of the refinement assumption.
- **Kind:** `general theorem` (almost direct from the definition of `committed`; trivial in proof effort).

### Claim 5
## `ControlStack.TrustedBroker.trace_preserves`

- **Says (plain English):** If a state `s` is Safe and `t` is reachable from `s` by any finite sequence of model steps, then `t` is Safe.
- **Under these hypotheses:** `Safe s` and `Trace roles s t`.
- **Does NOT say:** Same limits as `transaction_preserves`: no approval, review or sink content; model steps only. The trace relation includes any serial order of committed transactions but "excludes snapshot rollback and partial external effects" by construction, so a real rollback is outside the model.
- **Kind:** `general theorem` (induction over the trace from `transaction_preserves`).

### Claim 6
## `ControlStack.Deployment.TranscriptReplay.final_safe`

- **Says (plain English):** The final model state `s10` of the replayed transcript is Safe: spent (2) is at most cap (2); releases at most spent; consumed nonces distinct; every lease within budget.
- **Under these hypotheses:** None as a statement; it follows from `runtime_trace` plus `trace_preserves`. The same caveats as `runtime_trace` about whether the recorded log is the true run apply.
- **Does NOT say:** (a) It says nothing about the real database or sink, only about the model state obtained from the transcript. (b) Safe does not include any approval or review facts. (c) It does not show the transcript is complete: the omission examples show that a truncated transcript also passes.
- **Kind:** `finite computation (decide/native)` for the instance (derived from the general `trace_preserves`).

### Claim 7
## `ControlStack.Deployment.TranscriptReplay.replay_was_not_allowed`

- **Says (plain English):** In the model state `s8` reached just after the first release (nonce 1), the request `q8` (which has the same fields as the first release's request, so the same nonce) fails the release guard, whatever clock value, approval record and lease are offered. That is the model's explanation of the recorded denial in step 8.
- **Under these hypotheses:** None beyond the definitions; it quantifies over every clock value `now`, approval `a'` and lease `l'`.
- **Does NOT say:** (a) It does not show the real broker denied the real replay for this reason; the checker takes any recorded denial as an identity step. (b) It does not exclude replays under a different nonce. (c) It is a consequence of `committed_nonce_unusable`.
- **Kind:** `definitional/trivial` (a direct instance of `committed_nonce_unusable`, closed by `rfl`).

### Claim 8
## `ControlStack.Deployment.TranscriptReplay.omitted_tail_is_accepted`

- **Says (plain English):** The replay checker also accepts the transcript with its last receipt (the second release) removed: the first nine receipts form a valid shorter chain. A companion theorem (not translated here) says the end state then differs from the full one.
- **Under these hypotheses:** None (a closed finite computation by `decide`).
- **Does NOT say:** It is a limitation, not a safety claim: the checker verifies the chain but not completeness. A transcript that omits trailing events is indistinguishable by this checker from a complete one. It also is not a claim that this particular truncation happened.
- **Kind:** `negative control (shows a weakened model fails)` (more precisely, it demonstrates a blind spot of the replay checker), also `finite computation (decide/native)`.
