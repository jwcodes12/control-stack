# Review dispositions: Astra and Opus 5.5

The user explicitly requested both reviewers. Astra reviewed local sources read-only.
Opus reviewed an earlier pasted snapshot through the authenticated Claude CLI after
explicit user approval for repository-source transmission. Its source snapshot
predates some fixes and did not include every attacker/task file. Both reviews are
preserved under `reviews/egress-*-2026-10-08.md`; no approval or reviewer verdict is
being treated as a security certificate.

| Finding | Disposition |
|---|---|
| Partial fetch / OSError can appear as useful task success | Require successful honest response, local task completion, exact test output and matching pinned wheel digest; regression test |
| Shared-network mutation tests validator rather than packet oracle | Separate namespace rejection and failed-SYN packet-oracle mutations |
| Direct-to-mirror bypass can appear permitted | Add direct-mirror attack and host mutation; correlate mirror SYN source tuple with prior gateway socket attempt; independently trace connect syscalls |
| Packet-buffer loss unreported | AF_PACKET statistics; any dropped packet fails absence evidence |
| Mount/authority validation incomplete | Actual mountpoint allowlist, read-only system/code/config checks, all namespace-process socket FD checks; trusted runtime tree and kernel still explicit assumptions |
| Only current process descriptors inspected | Inspect every visible namespace process for socket descriptors before relay/task launch |
| Denial verdict permits logged allow/connect failures | Denied parser cases require deny decision and no allow/attempt/connected record; denied direct cases cannot touch mirror; redirect's initial permitted mirror visit is separately scoped |
| Slow-header saturation | Absolute two-second header deadline; 72 stalled-client test and observed honest recovery |
| Secret checks only plaintext mirror | Include decrypted TLS mirror observations; add secret-tls-tunnel counterexample |
| CONNECT Host default port ambiguity | Strict declared grammar requires Host to match chosen authority; honest TLS adapter test sends `Host: mirror.internal:443` |
| IPv6 extensions / IPv4 fragments misclassified | Decode supported IPv6 extension chains and TCP flags; do not interpret non-first fragments as transport ports; record all ::1 traffic |
| Observation filtered to fixture rather than arbitrary host traffic | Explicit unresolved deployment obligation; gateway syscall tracing independent and process-scoped; full all-destination outer topology remains next slice |

The implementation has followed the reviewers' concrete oracle proposals. Runtime
results remain fixture-scoped; the Lean proof remains conditional on the topology
and implementation correspondence premises.
