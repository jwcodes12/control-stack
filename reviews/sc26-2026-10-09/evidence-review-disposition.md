# Disposition: Gemini 3.1 Pro review of the SC-26 evidence package (run-1)

**Input caveat.** The package given to Gemini omitted three things:
- the receipt's `harness_sha256` field;
- the separately produced `h3-difftest.json`;
- the rechecker `tools/check_sc26_case.py`.

So several of its "not supported" verdicts rest on missing input, not on defects. Each point:

| Finding | Disposition |
|---|---|
| H3 not run (the runner has no difftest) | **Input artifact.** `lean_difftest.py` ran on the same commit after the runner, at the pinned seed. Output: `evidence/run-1/h3-difftest.json` (200 cases, 0 mismatches, coverage met). Prereg v2 does not require H3 to run inside `run_sc26.py`. |
| H5 self-test skipped | **Input artifact.** `tools/check_sc26_case.py` runs `check_trace --self-test` on the evidence: all mutations fail as required. |
| Controls: the model reproducing the ledger was not asserted | **Fixed in the rechecker.** `check_sc26_case.py` now requires `b_world == []` for every control, and all 7 pass. The runner's own control summary did not assert it; the prereg requirement is now checked from the raw data. |
| Dirty tree; no hash proof | **Partly an input artifact.** The receipt has `harness_sha256` and `lean_model_sha256`, and all 15 pins match (`check_sc26_case.py` PINS). The dirty flag lists only untracked files from other work, none of them SC-26 files. |
| c4 blind spot: recovery re-sends are not in the gate trace, so a buggy post-HALT re-send would read as in flight | **Valid checker blind spot.** The implementation is correct: recovery returns immediately when halted, and each re-send re-checks `halted` under the halt lock. The checker cannot see a re-send, though. **v3:** log every transmission, including re-sends, and make c4 fail on any transmission logged after the HALT. |
| Bank events are appended at the end of the replay, not interleaved | **Known, documented caveat.** Gate operations never read bank state, so final-state equality is valid, but the per-step `Inv` at bank events uses the final gate state. **v3:** both processes stamp `CLOCK_MONOTONIC` (shared on one host), and the checker interleaves by it. |
| c2 type confusion | **Not an issue.** Payloads are validated as `nat` ints on entry (`common.tx_of`), and the consent logs store the same ints. |
| Attack: huge or float-coerced amounts | **Not a vulnerability.** `nat()` rejects non-int, negative and values ≥ 2^62 before any store. Python ints are exact, and spend never exceeds the cap. **v3:** add these as explicit attack cases (A16) for documentation. |
| Attack: socket or thread exhaustion (DoS) | **Availability, out of scope for the safety claim.** A stalled gate sends nothing. HALT delivery under DoS is an availability premise (`HaltLiveness.lean`). **v3:** add an availability probe (HALT latency under a connection flood) as a reported, ungated measurement. |
| Attack: mixed concurrency swarm | **Valid coverage gap. v3:** add A17, randomized concurrent request/approve/execute/deliver/halt across threads, checked by c1–c8 and trace replay. |
| §5 overclaims | The SC-26 result states criterion 5 (human review) as open, and calls correspondence *tested*, not proved. No change beyond the above. |
