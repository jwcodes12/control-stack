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

## Scenario testing: next gated run (planned; not executed)

**Current test decision: NO-GO for repeating the frozen 0.25-second usefulness gate on this TCG host.**
The unchanged VM replay already establishes an infeasible deadline for this setup
(both conditions 0/64 lifetimes, all sender/receiver invocations timed out).
A fresh result on this host at the same deadline would not resolve the cause.
The repaired guest link and resource-configuration controls are the verified
infrastructure baseline, **not** a completed scenario evaluation.

| Gate | Required test / acceptance | Status |
|---|---|---|
| A. Host and protocol selection | Prefer a host with usable hardware virtualization, or separately administered hosts with authorized access. Record actual KVM/guest support, boot/source/config hashes, host sharing and management assumptions. If retaining TCG, independently measure startup costs and **pre-register** a new deadline protocol before running it; never relabel the original failed gate. | **BLOCKED: host/access or owner-approved protocol decision** |
| B. Pair readiness | Provision a new isolated pair; check actual guest identities, disks, RAM, affinity, prohibited devices and the single trusted link. Exercise fixed health requests and resource-rejection controls. Record a fresh config hash/receipt; don't reuse H for a changed platform. | **NOT RUN on another host** |
| C. Honest SC-01 scenario | Replay the fixed eight-fault catalog with the same declared sampling unit (64 independent paired five-episode lifetimes), oracle, schema, lineage, ledger charges, and 90% lower-confidence-bound usefulness floor. Prefer the **unchanged 0.25 s** contract if feasible; otherwise run a separately identified, preregistered amended contract with its own baseline/mediated receipts. | **FAILED on current TCG; next run pending** |
| D. Adversarial channel falsification | In a **separate** preregistered experiment after explicit authorization, test cross-guest signal paths and receiver-visible timing/termination, host cache/storage/clock effects, allowed-link misuse, management-plane influence and unintended episode-count signals. Include positive controls, independent trials, source-bound receipts and mutation checks. A null result cannot prove channel absence. | **NOT RUN for the VM pair** |
| E. Correspondence and assurance | Reconcile *all* receiver observations and the actual five-view schedule against Lean's model, confirm durable ledger/lineage/no-rollback assumptions, and bind VM, gateway, proof, side-channel and usefulness evidence to exact revisions. Update assumption status only after the corresponding evidence exists. | **PENDING; case CONDITIONAL** |
| F. Realistic-agent extension | Treat any open-ended coding/agent task as a **new scenario contract** with its own Bad event, usefulness metric, receiver observation inventory, preregistration and baseline. The current catalog success on the single-host harness does not validate an LLM-agent workload. | **NOT STARTED** |

### Reproduction versus a *new* scenario run

These commands verify the **saved historical failure**; they do not boot VMs or
establish usefulness or confidentiality:

```bash
python3 gateway/vm/check_isolation.py --config gateway/vm/configs/local-20261008-final.json --receipt gateway/vm/receipts/qemu-provision-20261008-linkfix.json
python3 gateway/vm/test_isolation.py
python3 gateway/vm/check_usefulness.py gateway/vm/receipts/usefulness-20261008-linkfix.json
```

After an authorized platform is provisioned and the chosen protocol is frozen,
the existing runner/checker entry points for a **fresh** scenario receipt are:

```bash
# Run on the provisioned host with NEW, source-bound pair configuration.
python3 gateway/vm/pair.py --config /path/to/new-config.json --receipt /path/to/new-boot-receipt.json --health 8
python3 gateway/vm/check_isolation.py --config /path/to/new-config.json --receipt /path/to/new-boot-receipt.json --files
python3 gateway/vm/run_usefulness.py --config /path/to/new-config.json --output /path/to/new-usefulness-receipt.json
python3 gateway/vm/check_usefulness.py /path/to/new-usefulness-receipt.json
```

Paths above are placeholders, **not** commands validated for an alternative
hypervisor or a deadline-amended contract. The current checker pins the QEMU
TCG configuration, and the runner imports the original frozen SC-01 contract:
a KVM/multi-host port or a revised deadline needs corresponding checked
implementation/configuration and preregistration before reuse. The runner's
nonzero exit on a failed usefulness gate is a meaningful failure even when
`check_usefulness.py` accepts its receipt as internally consistent. Keep
historical, revised-protocol, and future side-channel receipts distinct.

**Do not promote to runtime recovery certification from VM isolation or
successful scenario completion alone.** In particular, two guests on the same
physical host still share host-managed resources. The counting theorem requires
the complete receiver observation to be the five padded views or a justified
uniform side-kernel domination certificate within the stated budget; see
[BOUND.md](BOUND.md). No new VMs, channel experiments, ACL/IAM changes, or
proof/assurance promotions were performed by this documentation update.

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
VM boot, usefulness replay or channel experiment. [VM verification CI](https://github.com/jwcodes12/control-stack/actions/runs/37851767586)
passed on publication commit `ef266336e0e45b1bd903a94d2c20340a42113848`;
[CI receipt](receipts/ci-verification-20261008.json). Subsequent publication edits
are status/CI-receipt documentation only; the checked VM sources are unchanged.
Auditgate, ACLs, IAM and host network settings are untouched by this publication.
