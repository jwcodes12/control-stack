# Trusted-stack primitive implementation and remaining validity gates

Implemented as a reference control stack with a durable SQLite event gate:
- trusted registrar identity from Linux SO_PEERCRED on an AF_UNIX socket;
- distinct OS agent/reviewer/approver/admin UIDs;
- content-addressed artifact reviews (F4) and exact-payload, expiry, one-use nonce approvals (F7);
- trusted, shared, transactional per-agent leases and global cap with revocation (F5/F8);
- atomic check-before-record, fail-closed state checks and irreversible sticky halt bit (F1/F3).

**The modeled release is exclusively a SQLite row. It is not a real
deployment, privileged syscall, network connection or executed process.**
The service cannot prevent an agent from doing dangerous work on another
resource not mediated by this broker. Tests are *not* an OS-verified refinement
proof or proof of external effects after a crash.

Run source-only and negative fixture tests:
\`python3 -m unittest discover -s trusted_stack -p 'test_*.py' -v\`.

Current blockers:
- Real OS-level mediation, authenticated deputies and kill/termination guarantee;
- anti-rollback trusted counter anchoring, clock/expiry honesty, signature/key custody;
- proof that checked release effects correspond to all actual harmful effects;
- rigorous compositional invariants across F1–F8, not only isolated models;
- a positive F6 audit allocation theorem under false positives and unknown recall;
- new hardware-accelerated SC-01 VM usefulness experiment and full observation bound;
- independent human expert statement review.

These shortcomings are not silently promoted by the new code. The permitted
native x86 KVM feasibility from \`reviews/assurance-priorities/host-port-readiness.md\`
does not imply a frozen workload pass or no shared timing channel.
