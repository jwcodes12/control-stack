# SC-01 VM hosting assessment — 2026-10-08

**Step 1: local QEMU TCG selected after John's acceptance on 2026-10-08.**
Hardware KVM and remote administration remain unavailable in the recorded checks.
Local guest boot is verified by the [final provision receipt](receipts/qemu-provision-20261008-final.json).
The application network link remains blocked; see the [current blocker](README.md#current-blocker--2026-10-08).
The earlier blocked
assessment and receipts below are preserved as historical observations.

Evidence: [read-only preflight receipt](receipts/hosting-preflight-20261008.json).
Receipt SHA-256: `c7518347d8531cc241312a60eaebf95d80cd07150902daf973e1f8134a0543da`.
It records timestamps, TCP and SSH outcomes, local kernel/CPU/NUMA information,
selected OCI metadata, and authenticated read-only API outcomes. The OCI probe
source is embedded in the receipt. No certificates, private keys or auth tokens
are included.

| Option | Observation in the receipt | Decision |
|---|---|---|
| Proxmox `localbox-pve`, `100.77.156.51` | Tailscale reports online. TCP ports 22 and 8006 each timed out after six seconds. | Direct administration unavailable in this check. Timeouts alone do not identify the blocking rule. |
| Proxmox via `claude-lxc`, `100.112.124.105` | TCP port 22 connects. Batch SSH with existing host-key verification denies both `opc` and `root`: tailnet policy does not permit that SSH user. | The permitted intermediary is reachable, but an authorized SSH principal/access method is missing. No onward connection or Proxmox capacity/config inspection was possible. |
| Two separate OCI instances | Current instance is `VM.Standard.A1.Flex` in `us-ashburn-1`. No local OCI config, CLI, SDK or cloud auth environment was found initially. An SDK loaded only under `/tmp` authenticated with the existing instance principal. `list_instances`, `list_vcns` and `list_subnets` in the current compartment each returned HTTP 404 `NotAuthorizedOrNotFound`. | No usable compute/network inventory or existing subnet verified. No launch attempted. Another existing profile or authorized compartment may work; quota, capacity, image, placement and CPU pinning remain uninspected. |
| Nested KVM on this box | `/dev/kvm` absent; no libvirt socket or QEMU/libvirt runner found. Local architecture is aarch64, with online CPUs 0–1 in NUMA node 0. | Nested KVM unavailable with the current device exposure. No modules, device nodes or host settings changed. Software emulation would not satisfy the requested KVM assessment. |

The existing local SSH configuration targets Proxmox as `root` with
`~/.ssh/localbox_pve_ed25519`; it has no configured jump route. The receipt records
only the key path, not its contents. No SSH forwarding route was created and no
ACL, firewall, IAM policy or network setting was changed. No VMs were created.

Oracle documents that instance-principal authentication can work without a local
credential config, while service authorization depends on IAM policy. Successful
authentication here did not establish provisioning permission. See
[Oracle: calling services from an instance](https://docs.oracle.com/en-us/iaas/Content/Identity/Tasks/callingservicesfrominstances.htm).
Tailscale controls SSH access by destination user as well as network reachability;
the observed rejection is recorded verbatim in the receipt. See
[Tailscale SSH](https://tailscale.com/docs/features/tailscale-ssh).

## Required next input

John must identify an existing permitted `claude-lxc` SSH user/access method, or
an existing OCI provisioning profile and authorized compartment/subnet. If those
require ACL/network changes, John decides them. This task makes none.

After access is available, resume at step 1 to inspect actual host capacity and
configs before selecting a platform. Then separately commit provisioning,
configuration checks with rejection fixtures, the frozen usefulness replay, and
the assumption-ledger update. No hypervisor/config-hash assumption is recorded
as satisfied before a VM pair exists and its configurations pass the checker.

No new channel experiment or usefulness replay ran. The case remains
CONDITIONAL and auditgate is unchanged. Configured resource separation would
still need explicit limits for hypervisor correctness, physical cache/timing
effects, management access, rollback and complete receiver observations.

The branch stays local: `.github/workflows/scenario-a.yml` runs
`gateway/scenario/cache_probe.py` on every push, so publishing it would trigger a
new channel experiment. No workflows were edited or dispatched for this report.

## Local VM follow-up — 2026-10-08

John requested another check of running VMs on this box. The additional
[feasibility receipt](receipts/local-vm-feasibility-20261008.json) records the
kernel's `CPU: All CPU(s) started at EL1` and `kvm [1]: HYP mode not available`
messages. Receipt SHA-256: `6b0651b1ec6afed377d58bfc24a477f92aaca0074e8d97424f1a70da227c0f7f`.
KVM is compiled into the kernel but has no usable device; merely
installing QEMU or creating a device node would not expose ARM hypervisor mode.
No kernel, module, device or network settings were changed.

[QEMU's documentation](https://www.qemu.org/docs/master/system/introduction.html)
supports full-system guest emulation with TCG without hardware virtualization.
The receipt's package lookup found QEMU 11.1.2 with an `arm64_linux` bottle.
This establishes a software package route, **not a passing local VM boot check**:
no QEMU installation or guest boot was performed in this follow-up.

Two TCG guests would have their own kernels and could use independently copied
disks and disjoint process CPU affinity. They would continue to trust QEMU and
the shared host OS. The host exposes only CPUs 0–1 in NUMA node 0, and its cache
topology reports shared CPU lists `0-1`. Thus software VMs cannot establish a
literal absence of shared physical host resources, and the proposed deployment
assumption must explicitly retain shared host, physical cache and timing limits.

John subsequently accepted QEMU ("Qemu seems okay"). Proceed with full-system TCG
guests, retaining the shared-host/emulator and physical cache/timing assumptions.
This acceptance authorizes provisioning; it does not discharge an observation
premise or establish a recovery bound. Provisioning must verify guest boot and
record the effective configurations before replaying the frozen usefulness gate.

## What establishes the recovery bound

The finite-view theorem is a mathematical result, not an experiment: exactly
five nine-valued views give 59,049 transcripts for an independent uniform 32-bit
secret. It applies to every encoder and decoder only if the receiver's complete
secret-dependent observation is covered by that carrier. Additional observations
need a justified fixed side kernel with a uniform domination certificate of mass
at most 65536/59049. A successful attack can refute that hypothesis; failure to
find an attack does not prove it.

QEMU checks establish only the declared VM/resource configuration. The usefulness
replay establishes completion for the preregistered task and sampling assumptions.
Shared host state, clocks and microarchitecture remain unresolved. No channel
experiments are authorized by this infrastructure task; the previous single-host
cache finding remains bound to its own receipt and is never pooled with VM runs.

Current final config hash:
`56a4dfa192003deaddf483ad008383ade9c0a2ca8d7eea0829fc401db7ff02a1`.
Boot/configuration checks pass; fixed-message infrastructure network health failed
on the final pair. No full VM usefulness receipt or runtime bound exists.
