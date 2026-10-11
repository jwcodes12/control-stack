# T4.4 Checked replay of the recorded Tier 2 transcript (done)

`ControlStack/Deployment/TranscriptReplay.lean` is **generated** by `tools/gen_deployment_transcript.py` from
`deployment/runs/tier2/containers-final/events.json` (clean case, ten recorded broker requests/responses; the input's
SHA-256 is in the module header). `tools/check_deployment_transcript.py` regenerates and compares it, builds it, checks the
axiom report, and runs falsifying controls.

## What is proved (kernel-checked, `propext`/`Quot.sound` only)

- Each recorded request/response, with numeric Compose UIDs (agents 23701/23702, reviewer 23703, approver 23704, admin 23700),
  is a `TrustedBroker.Step` over a complete model state. A denied response is an identity step.
- The ten receipts are accepted by `CheckedTrace.verified` (`transcript_checked`, by `decide`), so by
  `indexed_receipts_sound` the transcript is a `TrustedBroker.Trace` from `initial 2` (`runtime_trace`).
- The end state is `Safe` and `Coherent`, with cap 2, spent 2, releases 2, consumed nonces `[2, 1]`, not halted
  (`final_safe`, `final_coherent`, `final_counts`).
- The recorded replay of nonce `a` is a model denial: the request is not `Allowed` after the first release whichever approval
  and lease the caller names (`replay_was_not_allowed`).

## Omission examples (what transcript checking cannot catch)

- Dropping a state-changing receipt from the middle is **rejected** (`omitted_state_change_is_rejected`).
- Dropping the last receipt is **accepted** and the end state differs (`omitted_tail_is_accepted`,
  `omitted_tail_changes_the_end`): the checker cannot tell a complete log from a truncated one.
- Dropping the denied replay breaks the chain of recorded state ids (`omitted_denial_breaks_the_id_chain`), but a producer
  that renumbered a shorter log consistently would be accepted: the checker only sees the receipts it is given.

## Falsifying controls

Three mutated transcripts do **not** elaborate (checked in `check_deployment_transcript.py`): the release by an agent other
than the approved one, a second release of the same nonce reported as accepted, and a review by a non-reviewer UID.

## Limits (not claimed)

- No timestamp was recorded. `now = 0` is a feasible witness for the expiry guards, not the broker's clock.
- Completeness and authenticity of the log are premises, not results.
- The link from model releases to sink files is the receiver refinement premise (bytes are checked by
  `deployment/check_container_run.py`, not here).
- This is one archived clean-case transcript from source generation `r2-v0`, not a statement about the current broker code.

## Why the first three attempts failed (Sol, Tier 4)

The generated proof terms used `by try simp only [R]; all_goals decide`. Lean parses that as `try (simp only [R]; all_goals decide)`,
so when `simp only [R]` failed the whole block was silently skipped and the goal was left unsolved; this produced the
"unsolved goals `s0.halted = false` ..." diagnostics (deployment/runs/tier4/transcript-prototype-attempt3.txt). Separately, the
reviewer-existential argument sat in the wrong position of the 21-conjunct `Allowed`. The fix was to state each obligation
with a small `first | rfl | Or.inl rfl | Or.inr rfl | decide` macro, which the kernel evaluates directly on the concrete states
(`put` unfolds on numeric literals), with the argument order taken from `TrustedBroker.Step`.
