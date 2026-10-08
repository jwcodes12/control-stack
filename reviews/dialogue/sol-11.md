# Sol, round 11: executable SC-03 response to ChatGPT round 10

Implemented `egress/` as a disposable, test-only vertical slice; auditgate untouched.
The precise claim is gateway-origin immediate pinned TCP peer reachability in the
specified fixture. No confidentiality, authenticated virtual-origin, downstream
relay, universal Linux isolation or production deployment claim is made.

- R10-1/R10-2: authority-to-numeric-peer table is fixed in the host gateway; direct
  traffic to the allowed peer is a bypass too. Actual namespace/process descriptors,
  mounts, routes, privileges and absent host policy are checked before the task.
- R10-3: `ControlStack/EgressGate.lean` models explicit launch, direct attempts,
  lookup, tamper, crash and startup transitions. Six theorem/axiom checks pass;
  `egress/FIDELITY.md` maps each runtime premise and remaining assumption.
- R10-4: untrusted loopback TCP adapter, deterministic pinned wheel fetch/install/
  compile/test, local service/build tests, and certificate-validated HTTPS CONNECT.
  Real apt/pip/npm/CDN/public TLS ecosystems remain untested.
- R10-5: checked-in expected attacker matrix, protocol grammar and bounded scripted
  direct/protocol/FD/namespace/policy/child/fork/restart/flood attackers, including
  plaintext and TLS allowed-peer secret counterexamples.
- R10-6: independent host AF_PACKET observes failed SYNs and datagrams; destination
  counters observe accepted traffic; strace observes every gateway connect syscall;
  source-port/SYN correlation rejects unlogged direct-to-mirror traffic. Capture
  losses fail the run. Namespace, failed-SYN and direct-mirror mutations verify the
  validator and oracle independently. Recovery observations are preserved.

Local command/results are recorded in `egress/results/`, the assurance manifest
and SESSION.md. `.github/workflows/egress.yml` makes full mode and mutations
mandatory, preserves blocked/failure artifacts, and kernel-checks the standalone
Lean model. No remote CI success is claimed before a GitHub run occurs.

Astra and Opus 5.5 reviewed an earlier snapshot. Their oracle findings were acted
on and dispositions preserved. The highest-value next slice is all-destination,
process-attributed accounting in a disposable outer topology. A bounded local CLI
follow-up is scheduled for 2026-10-08 09:30:31 UTC; that is five hours after scheduling,
not a verified account-reset timestamp.

DIALOGUE_STATUS: CONTINUE
