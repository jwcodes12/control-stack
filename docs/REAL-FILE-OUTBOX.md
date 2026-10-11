# Narrow trusted filesystem effect receiver

**Scope and status.** A trusted administrator can take an *already-committed*
`effect_records` entry from the SQLite authorization controller and publish
exactly its recorded artifact body to one preconfigured, broker-owned filesystem
directory. This is a **real host filesystem effect**, not an arbitrary-action
reference monitor, code execution, network mediation, deployer, or payment path.
Nothing here proves that the untrusted model cannot use another syscall/path.

## Trust boundary and bootstrap

The broker must run under a UID distinct from all untrusted agent UIDs and
own both the `0600` SQLite file and a pre-created `0700` output directory.
Supply that directory to the trusted process as `--effect-root /trusted/output`.
The **RPC requester cannot choose the root or output filename**. Only a UID
listed in the `admins` group (derived via Linux `SO_PEERCRED`, never a request
field) can ask `{"op":"publish_effect","release_id":1}`. The agent can still
request `effect_release` only with a previously reviewed digest, independently
signed approval, active lease, exact destination and unused nonce.

The published name is `effect-000000000001.bin` for release 1, independent of
the untrusted logical destination string. The receiver uses a directory file
descriptor, `O_NOFOLLOW`, `O_EXCL` temporary files, `fsync` on the content,
and a no-overwrite `link` to the final name followed by directory `fsync`.
It rejects symlinks, output ownership or mode violations, existing files with
different bytes, mismatched SHA-256 payloads, revoked/expired leases, and HALT.
The SQLite `BEGIN IMMEDIATE` writer lock orders publication against HALT,
revoke and other broker writes. File publication neither spends additional
budget nor re-consumes the nonce.

**Crash reconciliation:** If a crash follows publication but precedes reply,
a retry reads and verifies the same committed bytes at the same filename.
If a crash occurs before the final link, the committed outbox remains available
for later retry, subject to the new HALT/lease checks. Orphaned temporary files
are possible across abrupt power loss; output directory health and cleanup
belong to a trusted operator. No attempt is made to atomically commit SQLite
and an external filesystem as one distributed transaction.

**Critical premises:** trusted broker UID and root directory; safe parent
directories/mount topology; cooperative filesystem `fsync` durability;
no untrusted same-UID writer or alternate effect path; trusted OS, clock, review
and approval personnel. A compromised broker, hostile mount, or adversary with
write access to the root voids the guarantee. A pre-existing file with the
same verified bytes is reconciled, not linked again. Output visibility may
precede successful response; clients must treat timeouts as ambiguous.

## Reproduce

```bash
python3 -m unittest trusted_stack.test_publish_effect -v
python3 -m unittest discover -s trusted_stack -p 'test_*.py' -v
lake exe cache get
lake build ControlStack.GateComposition
lake env lean reviews/family-strengthening/RuntimeGates.lean
```

The source-bound F6 weighted-history lemma quantifies over *every* considered
history, assuming bounded conditional miss and false-alarm rates and normalized
weights. It **does not establish** empirical values or lack of attacker
visibility into audit feedback. F8's joint interleaving model establishes a
shared arithmetic budget and sticky HALT for the abstract admission semantics,
not mediation completeness, real concurrent syscalls or interrupt cancellation.

## Unresolved deployment/research gates

1. Enforce a privileged syscall/process/network policy against **all** relevant
   untrusted paths, including same-UID escape, trusted deputy, container/device,
   in-flight action and privilege transitions. This adapter only publishes files.
2. Prove/refine a concrete OS-broker execution relation to the relevant Lean
   transition system, preserving actual effects and observations under crashes,
   power loss, scheduling and HALT.
3. Calibrate per-history conditional monitor recall and false-positive rates
   on held-out adaptive traces; independently audit sampled population/weights.
4. Run SC-01's **unchanged frozen usefulness protocol** on an authorized native
   hardware-accelerated VM or separately re-preregistered port. The original
   ARM TCG receipt had 0/64 useful baseline and 0/64 useful mediated runs.
5. Obtain genuinely **independent** expanded-statement review, trusted role
   and credentials custody verification, and measured normal-task usefulness.

None of the 28 scenarios should be promoted to deployment-assured by this PR.
Historical preregistrations, evidence and `ControlStack/EgressGate.lean` are
untouched. See root `COMPLETED.md` and `RUNTIME-VM-HANDOFF.md`.
