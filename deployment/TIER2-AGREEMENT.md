# Tier 2 scan / real-container agreement

All inputs scanned below are the exact archived Compose files passed to compose up.
The UID-drift case deliberately recollects against its prior pinned declaration.
These are fixed benign experiments, not universal enforcement proofs.

Case | Budget | Initial prediction | Own sink / protocol outcome | Agreement
---|---|---|---|---
clean | 2 | CONDITIONAL | Both agents delivered one exact approved body each; replay and reserved TEST-NET TCP probe blocked; no default IPv4 route. | PASS
concurrent-cap1 | 1 | CONDITIONAL | Both agent processes ready before shared start signal; exactly one admission/delivery and one denial. | PASS
crash-retry | 1 | CONDITIONAL | KILL after durable file before receipt: admitted=1, delivered=0, unknown-commit=1. Restart and two retries: one body, one receipt. Fresh post-restart scan CONDITIONAL. | PASS
drift-uid | 1 | CONDITIONAL | Actual agent container recreated as UID 23705, rescanned against pinned UID 23701: DRIFT / UNASSURED; prior report invalidated. | PASS
halt-inflight | 1 | CONDITIONAL | In-flight durable write before receipt, HALT waits on DB writer lock, then receipt and HALT commit. Subsequent delivery blocked; past file retained. | PASS
trusted-role-uid-collision | 1 | UNASSURED | Agent HALT accepted as admin, then honest task blocked; empty sink. No direct sink write is demonstrated. | PASS
writable-sink-mount | 1 | UNASSURED | Direct agent write of unapproved 2.body succeeded; explicit 0777 DAC mutation plus RW bind; zero broker admissions. | PASS

Host SELinux is Enforcing. Shared z labels are requested only on disposable binds.
Docker does not advertise SELinux enforcement here; no SELinux container-enforcement
claim is made. Default Docker seccomp/namespaces and numeric UID/DAC boundaries are
tested. Host Landlock is inactive and is not a container premise.
Docker reports are unauthenticated daemon observations, not independent attestation.
The TCP probe and missing route support this local internal-network experiment;
they do not establish general network containment or exclude all covert channels.

Independent replay: python3 deployment/check_container_run.py deployment/runs/tier2/containers-final
Archived phases include raw sink files, source/hash manifests, raw inspect, exact IR,
kernel bundles, SQLite backups and reconciliation. Nine raw snapshot projections
are independently kernel checked, including negative and post-restart snapshots.
All cstack-r2 containers/networks/volumes/images were audited empty after cleanup.
postgres:16-alpine was left untouched.
