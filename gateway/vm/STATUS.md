# SC-01 VM infrastructure status — 2026-10-08

**Step 4 is blocked by a failed usefulness gate. The case remains CONDITIONAL.**
Two QEMU TCG guests boot and the checked configuration passes the resource
controls. The repaired transport works in the saved boot receipt. The unchanged
SC-01 usefulness replay completed zero lifetimes in either condition. These
checks do not establish a runtime secrecy or safety result.

## Evidence

All VM receipts below bind configuration hash H:
`56a4dfa192003deaddf483ad008383ade9c0a2ca8d7eea0829fc401db7ff02a1`.

| Step | Status | Evidence |
|---|---|---|
| 1. Hosting decision | Local TCG accepted by John; hardware KVM unavailable on this ARM64 host | [HOSTING.md](HOSTING.md), [host feasibility receipt](receipts/local-vm-feasibility-20261008.json) |
| 2. Provisioning | Pinned images; distinct guest kernels/boot identities, separate raw disks, nonmerged guest RAM; QEMU A pinned to CPU 0 and B to CPU 1, both on NUMA node 0 | [configs](configs/local-20261008-final.json), [image lock](image.lock.json), [boot/QMP/thread/link receipt](receipts/qemu-provision-20261008-linkfix.json) |
| 3. Configuration checker | Pass on H and historical live snapshot; 10 tests pass, including seven resource rejection fixtures | [checker receipt](receipts/isolation-check-20261008-linkfix.json), [controls](receipts/isolation-controls-20261008-linkfix.json), [publication verification](receipts/publication-verification-20261008.json) |
| 4. Frozen usefulness replay | **FAIL**: baseline 0/64 lifetimes and 0/320 episodes; mediated 0/64 lifetimes and 0/320 episodes | [full VM receipt](receipts/usefulness-20261008-linkfix.json), verified by `check_usefulness.py` |
| 5. Assumption ledger | Pending after failed step 4; existing correspondence and assurance files unchanged by this publication | Gate failure above; [proof obligations](BOUND.md) |

The fixed task, 64 paired lifetimes, five episodes, 0.25-second agent deadlines,
90% floor and confidence procedure were preserved. Both agents timed out in
all 640 condition episodes (1,280 process invocations), as recorded in the
full receipt. Median episode wall time was 2.294 seconds for baseline and
1.931 seconds for mediated. Slow execution under TCG is the working explanation;
the receipt does not isolate the cost of each startup component. Results remain
separate from the single-host runs. No new channel experiment was run here.

## Next step

Select a host with usable hardware virtualization or two separate physical/cloud
hosts and attempt the same frozen usefulness gate there. Existing permitted
access is still needed; John decides network/ACL changes. A deadline amendment
would require a separate preregistration and John's decision; no amendment or
rerun is included in this publication.

Passing the gate would still leave the complete-observation proof obligation.
The original “no shared host resources” requirement is not met by two guests
on this box: host OS/QEMU, physical caches, timing, memory bus and physical
storage remain shared. The checker covers configured resources and historical
snapshots, not hardware separation or universal leakage. Host/emulator integrity,
management channels, rollback and fixed-horizon correspondence remain assumptions.
See [BOUND.md](BOUND.md).

## MXC assessment

Checked the Microsoft MXC documentation at commit
[`e157fa4`](https://github.com/microsoft/mxc/tree/e157fa4bbde7a3a81198ef36a04c5003458de535).
It could provide a reusable sandbox API, but it does not resolve this host's
virtualization limitation: Linux defaults to [bubblewrap](https://github.com/microsoft/mxc/blob/e157fa4bbde7a3a81198ef36a04c5003458de535/README.md);
[Nanvix MicroVM](https://github.com/microsoft/mxc/blob/e157fa4bbde7a3a81198ef36a04c5003458de535/docs/backends/nanvix/nanvix.md)
requires `/dev/kvm` on Linux; [Hyperlight](https://github.com/microsoft/mxc/blob/e157fa4bbde7a3a81198ef36a04c5003458de535/docs/backends/hyperlight/hyperlight-backend.md)
requires x86_64 and KVM. This box is ARM64 without KVM, per the feasibility
receipt. MXC was inspected, not installed or substituted into the experiment.

## Publication and reproduction

VM sources and historical receipts were imported from branch
`sc01-vm-host-check-20261008` at `9d4d785`. Codex's infrastructure work ends at
`9a43ae8`; Claude's subsequent commits `cda2b10` and `9d4d785` repair the link and
record the failed replay. Those results were verified from the publication
checkout. Only the VM directory, its CI workflow, HANDOFF and ROADMAP are
published here; other local work and unrelated untracked drafts are excluded.
Existing remote-main Lean work is preserved.

```bash
python3 gateway/vm/check_isolation.py --config gateway/vm/configs/local-20261008-final.json --receipt gateway/vm/receipts/qemu-provision-20261008-linkfix.json
python3 gateway/vm/test_isolation.py
python3 gateway/vm/check_usefulness.py gateway/vm/receipts/usefulness-20261008-linkfix.json
```

The usefulness verifier passing means the failed receipt is consistent with
its source/configuration bindings; it does not mean the usefulness gate passed.
The publication verification receipt records these checks and their source hashes.

Automatic push CI is skipped for this publication because the existing scenario
workflow runs a new cache experiment. Only `vm-isolation.yml` is dispatched:
saved configuration and receipt verification plus rejection controls, with no
VM boot, usefulness replay or channel experiment. Remote CI status is pending.
Auditgate, ACLs, IAM and host network settings are untouched by this publication.
