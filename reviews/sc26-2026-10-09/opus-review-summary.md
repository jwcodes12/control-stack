# Opus 5.5 adversarial review of SC-26: summary of findings

The reviewer is a Claude Code subagent, Opus 5.5. It is the same model family as the author, so this is NOT a
foreign-family red team. It reviewed the model after the send/arrive split, and the harness at the time of review.
It made 22 tool calls, including brute-force searches to depth 7 and Lean probes.

**Verdict:** `sc26_safe` holds as stated, and brute force found no violation of `Good`. But the prose overstated:
- "approval" meant only an `approve` operation that carries an approver identity;
- "independent" meant only a different id from the requester;
- "one-use" came from the bank's deduplication;
- HALT does not stop payments that are already in flight.

The prereg was frozen before the model and harness it governs were committed.

| # | Finding | Disposition |
|---|---|---|
| D1 | The approval is a provenance tag. The adversary can issue `approve 2 …` itself. The docstring said `legal` is the only premise. | Docstring corrected. Consent needs credential separation for approvers, which is now stated in the theorem docstring, the header, threat.md and correspondence.md. The runtime enforces it with SO_PEERCRED; attacks A2, A3 and A13 test it. |
| D2 | No role-disjointness premise: with overlapping roles, colluding agents approve each other. The `distinct` check is redundant when roles are disjoint. | Added `sc26_safe_disjoint`: with disjoint roles, every payment's approver is not an agent. Role disjointness is now a stated premise. The `distinct` control runs with overlapping roles, recorded in its config. |
| D3 | HALT doesn't stop payments that are in flight, contradicting threat.md and prereg v1. Runtime recovery resent unacknowledged intents after HALT. | threat.md reworded to "no payment initiated after HALT". The runtime may not send or resend anything while halted. A new crash point, after the intent is recorded and before it is sent, is exercised. Prereg v1 is superseded by v2 (see below). |
| D4 | One-use comes from bank deduplication, not the gate's nonce. Without deduplication the cap breaks too. `no_dedup_retry_duplicates` showed only a duplicate key. | `safe_of_sound` and `good_without_nonce` now state this. `no_dedup_breaks_cap` (bank total 30 vs spent 10) added. The header says safety needs an idempotent receiver. Non-idempotent effects are out of scope for this design. |
| D5 | `Good` doesn't say an approval is consumed at most once. | Added `sc26_once`: reservations are unique per request id in the deployed configuration. |
| D6 | The same invoice paid twice, under two request ids, is `Good`. | Added `same_payload_twice_is_good`, which documents that exactly-once is per request id. The runtime checker adds c8, a business-level exactly-once rule keyed on memo. |
| D7 | No necessity witness for `bankAuth`. | Added `no_bank_auth_breaks`. |
| D8 | `execute` ignores its caller. The model reimplements halt instead of using `withHalt`. A halt between reservation and send strands budget. | Documented in the header. Stranded budget after a halt is an availability effect only. |

**Prereg loopholes:**
- **Freeze didn't pin the artifacts.** Prereg v1 (commit 95e3575) was frozen while the model and harness were
  uncommitted, and the model then changed. **v1 is superseded before any evidence run.** v2 pins the SHA-256 of the
  model, harness and checker inside the prereg text itself.
- **c3 couldn't fire.** It now uses the approver's own log together with role disjointness.
- **The H5 pass rule was too loose.** Each control must now produce its specific finding.
- **No coverage requirement for H3.** v2 adds one.
- **Re-runs weren't bound.** An evidence label is refused unless the output directory and the prereg hash match.
- **A crash window was missing.** It is now covered.
- **H4 tolerated double payment.** v2 fails on any double payment of one invoice.

**Novelty:** none. This is a textbook reference monitor with a two-person rule, idempotency keys, a budget and a
kill switch. Agreed.
