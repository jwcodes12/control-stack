# SC-01 QEMU guest pair

Current evidence and next step: [STATUS.md](STATUS.md).

This infrastructure uses full-system QEMU TCG emulation because the OCI host
does not expose ARM hypervisor mode. John accepted this route with its explicit
shared-host limits. It is not hardware KVM and does not establish a recovery
bound. See [hosting decision](HOSTING.md).

VM-A contains the trusted gateway, durable SQLite ledger and sandboxed sender.
VM-B contains a trusted receiving service and sandboxed receiver. Each has an
independent kernel/initial RAM filesystem file and a separate raw ext4 root/state
disk, with no overlay backing image. The boot init switches onto that disk before
running bubblewrap; the initial rootfs cannot support its pivot operation.
Whole-process CPU affinity pins every
QEMU thread to CPU 0 for A and CPU 1 for B; both belong to host NUMA node 0.
Anonymous guest RAM disables sharing and merging. No guest filesystem mounts
host directories.

The only guest network device in either VM is a virtio interface on a single
QEMU socket link over host loopback. There is no user-mode NAT, host forwarding,
tap, bridge, default guest route or internet interface. The trusted A gateway
connects to the trusted B service on that link. Agents get fresh bubblewrap
network/PID/IPC namespaces within their respective guests, no capabilities and
no view of the service, serial console or ledger. Their only application I/O
is supplied stdin and captured stdout. Root guest supervisors and the host
operator remain trusted; a device count alone does not prove this enforcement.

Independent serial pipes and QMP Unix sockets connect only to the trusted host
supervisor. They are management channels, not part of the untrusted agents'
view. Protecting them and preventing secret-dependent host decisions remain
assumptions.

## Provision and inspect

Install QEMU 11.1.2 (the saved configurations bind the installed executable's
hash). The pinned image lock binds Alpine 3.24.2 aarch64, the static APK tool and
every downloaded package by SHA-256. Packages are installed into the guest root
offline, with scripts disabled; this does not install Alpine packages on the
host. Download trust remains an upstream/HTTPS assumption.

```bash
sudo /usr/bin/python3 gateway/vm/provision.py --output /var/tmp/sc01-vm-pair-NEW
python3 gateway/vm/pair.py --config /var/tmp/sc01-vm-pair-NEW/config.json \
  --receipt /tmp/sc01-vm-provision-NEW.json
```

The output directory and receipt must be new: there is no automatic replacement
of images, ledger state or evidence. Image assembly needs root for guest file
ownership; QEMU boots as the invoking ordinary user. The pair script stops both
guests after collecting the receipt. This boot/preflight is infrastructure
verification, with no secrets, repair task or channel measurement.

The receipt saves both full QEMU commands and initial image hashes, plus live
process argv, every thread's CPU affinity, QMP CPU/block/chardev/memory/status
queries, and guest kernel/boot identities and namespace preflights. Saved raw
disk hashes describe initial disk bytes: writable state subsequently changes.
The read-only kernel and initial RAM filesystem hashes continue to bind the
guest boot inputs. The guest root/state disk is writable by its trusted
supervisor; the receipt also records the loaded application source hashes.
The config hash covers the canonical JSON configurations
and source/image pins, excluding the volatile PID/boot observations.

## Proof and evidence limits

Exactly five nine-valued views give 59,049 transcripts. The counting theorem
bounds exact recovery of an independent uniform 32-bit secret by
59,049/2^32, conditional on covering complete receiver information. With a fixed
side kernel and a uniform domination certificate of lifetime mass L, the bound
becomes 59,049 × L / 2^32; the 2^-16 target needs L ≤ 65,536/59,049 (~1.11).

Configuration rejection controls establish only the listed configuration
restrictions. A usefulness replay establishes task completion at the frozen
floor under its sampling assumptions. Neither proves a universal upper bound on
side observations. The prior single-host cache receipt remains evidence about
that configuration; failure to observe an attack in another configuration would
not prove that its side certificate exists.

Shared host kernel/emulator correctness, shared physical cache and timing,
management channels, disks' physical storage backend, NUMA memory bus, clocks,
host services on either CPU, supply chain, snapshot rollback, statistical
independence and complete receiver observations remain outside these checks.
The case stays CONDITIONAL. No channel experiments are part of this task.

## Saved local provisioning check

[Full provision receipt](receipts/qemu-provision-20261008.json),
[VM configurations](configs/local-20261008.json): both guests booted Linux
6.18.55-0-virt with distinct boot IDs. Their agent namespace preflights passed;
every recorded QEMU thread had affinity `{0}` for A and `{1}` for B. These are
configuration/boot observations only. Config hash:
`255c3c3c393a350019d6e90305c434aca45d5c044a4e805cc645dd7f86cc59c7`.

## Configuration rejection controls

```bash
python3 gateway/vm/check_isolation.py --config gateway/vm/configs/local-20261008-final.json \
  --receipt gateway/vm/receipts/qemu-provision-20261008-final.json
python3 gateway/vm/test_isolation.py
```

Add `--files` on the provisioning host to inspect current file inode aliases,
read-only boot-file hashes and the QEMU binary hash. Writable root/state disks
are checked for path/inode separation; their initial contents are recorded in
the provisioning receipt and are not expected to retain that hash after boot.

The checker parses the complete QEMU argument lists and rejects unknown flags
and devices. It also checks the archived live process arguments, thread affinity,
raw block devices without backing chains, memory/chardev queries, application
hashes and per-guest agent network/PID/capability preflights. An archived snapshot
is historical evidence, not attestation of a currently running VM.

Seven single-change fixtures reject shared disks, 9p, virtiofs, shared memory,
a second network path, overlapping CPU pinning and an extra config include.
Additional controls reject hardlink/symlink aliases, live argv/affinity drift,
duplicate boot identities and enabled RAM merging. Results:
[configuration check](receipts/isolation-check-20261008-final.json),
[negative controls](receipts/isolation-controls-20261008-final.json).
`vm-isolation.yml` runs the static saved-receipt check and controls in CI without
booting a guest or running a channel experiment. No remote CI result is claimed.

## Link fix — 2026-10-08

**Cause of the unreliable guest link.** QEMU's `-netdev socket,connect=` makes one
connection attempt and never retries. `pair.py` used to launch VM-B right after
VM-A. Whenever B's QEMU connected before A's QEMU had bound its listener, the link
stayed down for that whole boot, and QEMU reported no error. That matches every
failed receipt: both guests transmit, neither receives, A's neighbour entry stays
incomplete and the health request fails with EHOSTUNREACH. The one PCI run that
worked had simply won the race; MMIO vs PCI was not the cause.
[Negative control](receipts/link-race-control-20261008.json)
(`diagnostics/link_race_control.py`): starting B two seconds before A leaves A
listening and B's socket in TIME_WAIT, with no established pair.

**Fix (launcher only; configuration and config hash unchanged).** `pair.py` starts
the listening guest first. It waits for LISTEN in `/proc/net/tcp`, reading the
table without connecting, because a probe would consume QEMU's single accept. It
then starts the connecting guest and requires one ESTABLISHED host socket pair
before any guest traffic. The receipt records the host socket table at start and
at capture (`link`). `check_isolation.py` requires exactly one listener and one
mirrored established pair. Two new controls reject an extra peer and a missing
link.

Results on config `56a4dfa1…` (unchanged):
- five scratch boots, 20/20 health requests;
- [config-bound receipt](receipts/qemu-provision-20261008-linkfix.json), 8/8 health;
- [isolation check](receipts/isolation-check-20261008-linkfix.json) with `--files`: pass;
- [controls](receipts/isolation-controls-20261008-linkfix.json): 10/10.

Link health is an infrastructure check. It says nothing about channels: shared
host cache and timing remain unresolved ([BOUND.md](BOUND.md)).

## Usefulness replay on the repaired link — 2026-10-08: GATE FAILED (deadline infeasible under TCG)

[Receipt](receipts/usefulness-20261008-linkfix.json), verified by `check_usefulness.py`. Config `56a4dfa1…`;
link health OK. This is the frozen gate with nothing changed: original task, 64 paired lifetimes, five episodes,
0.25-second agent deadlines, oracle, 90% floor.

| condition | completed lifetimes | completed episodes | median episode wall time |
|---|---|---|---|
| baseline | 0/64 | 0/320 | 2.29 s |
| mediated | 0/64 | 0/320 | 1.93 s |

**Cause.** Sender and receiver both hit the 0.25-second deadline in all 640 condition episodes (1,280 process invocations). Starting bubblewrap and Python
inside a fully emulated (TCG) guest takes longer than the deadline that was calibrated on the host. The failure
says nothing about the cost of the schema: the baseline fails identically. The ledger behaved as specified: every
lineage was charged a product of 59049, and the sixth episode was refused.

**Consequence.** No VM usefulness pass exists, so step 5 (assumption ledger and manifest update) remains pending. The
SC-01 case and its manifests are unchanged and stay CONDITIONAL. Passing would need a preregistered protocol change,
which is the owner's decision. Two options:
- a deadline amendment, for example scaling by a separately measured guest/host slowdown, preregistered before any
  rerun;
- hardware-virtualised or separate hosts, where the frozen deadline is plausible.

Neither option bears on the separate probability-bound obligation ([BOUND.md](BOUND.md)).

## Historical transport failures — 2026-10-08

The earlier [final boot receipt](receipts/qemu-provision-20261008-final.json)
records four failed health requests. The initial replay produced an
[incomplete startup receipt](receipts/usefulness-startup-failure-20261008.json).
[MMIO](receipts/network-mmio-failure-20261008.json) and
[PCI](receipts/network-pci-health-20261008.json) diagnostics are retained as
historical evidence. These failures preceded the launcher race fix above.
The current blocker is the failed frozen usefulness gate; see [STATUS.md](STATUS.md).
