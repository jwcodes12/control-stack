# SC-01 usefulness recovery: native-accelerated guest port plan

**Status: design/host feasibility only; NOT a recovered usefulness result.**
All original evidence and preregistrations remain immutable. The frozen
`sc01-repair-catalog/1.0` task still requires exactly **0.25 seconds per
agent invocation**, 64 paired independent five-episode lifetimes and the same
confidence floor. The current aarch64/QEMU-TCG configuration failed 0/64
baseline and 0/64 mediated lifetimes.

## Verified host capability (no SC-01 guests, no new task trial)

- [ARM runner diagnostic #37880911299](https://github.com/jwcodes12/control-stack/actions/runs/37880911299): `aarch64` matches frozen guests, but **no /dev/kvm** exists. Not a native-accelerated host.
- [x86 root KVM ioctl #37881180806](https://github.com/jwcodes12/control-stack/actions/runs/37881180806): privileged ioctl returned **KVM API 12**; unprivileged probe was denied. This is an access/host-capability finding.
- [x86 QMP smoke #37881258339](https://github.com/jwcodes12/control-stack/actions/runs/37881258339): after installing packaged QEMU, a paused image-free `qemu-system-x86_64` reported **`query-kvm.enabled=true`**. No Linux guest boot or SC-01 task occurred.

**Engineering consequence:** an x86-64 KVM path is plausible, but the pinned
ARM64 kernel, Alpine rootfs, static APK packages and QEMU `virt-11.1`
machine cannot simply run accelerated under an x86 KVM hypervisor.

## Candidate routes

1. **Native ARM64 KVM host**: closest to the existing pinned guest binaries,
   but neither the original OCI ARM host nor the inspected standard GitHub
   ARM runner exposes usable KVM. A permitted ARM host would still need full
   config/source and observed isolation verification.
2. **Versioned native x86_64 guest port on available x86 KVM**: independently
   pin Alpine `x86_64` minirootfs + APK manifest and kernel/initramfs
   with checked SHA-256, adapt guest console/virtio/CPU device arguments,
   test no guest-host mounts/network bypass, preserve the unmodified
   application/oracle/deadline, and run full two-guest boot/health and negative
   isolation controls under a new configuration hash. The positive QMP
   accelerator smoke establishes only one prerequisite. This is **not** a
   no-change replay of the original ARM VM configuration; provenance and
   applicability must be separately evaluated.
3. **Two independently administered physical hosts**, if trusted link and
   independent instrumentation are available: may reduce shared-resource
   channels but management, network timing and observation completeness
   remain load-bearing.

## Acceptance sequence for *any* new route

- The owner identifies an authorized platform/VM cost envelope and approves
  any necessary compute or network changes. Never assume existing access.
- Freeze the **new host and image configuration** before measurement:
  tool versions, exact image/package hashes, source commit, hardware
  acceleration and CPU/resource ownership, endpoint inventory, side effects,
  management-plane trust, rollback anchoring and guest identities.
- Run a **non-SC-01 infrastructure health/agent-startup diagnostic** first,
  recording stdout/exit/timing without secrets. This prevents another 0/64
  execution on a known-infeasible platform and must not tune the preregistered
  task deadline from SC-01 success data.
- If the unchanged 0.25-second startup protocol is feasible, perform the
  **original** 64-lifetime SC-01 usefulness gate, source-bound under the
  new environment, not pooled with prior receipts. Check both baseline and
  mediated confidence bounds, 5-episode ledger and honest oracle.
- If infeasible, **do not reclassify the 0/64 result**. Any new deadline must
  be owner-approved and preregistered as a separate contract **before** that
  experiment, with independent data and distinct receipts.
- Independently falsify plausible unintended observations (timing, shared
  cache/storage, host management, termination, counters and side channels).
  A failure to detect a channel is not a proof of completeness.
- Only attempt a conditional deployment assurance once *both* usefulness
  and the appropriate all-observation/refinement premises have real
  evidence, with independent review and trust assumptions spelled out.

## Important no-go

The prior read-only executable-cache experiment recovered one secret bit
across 64/64 single-host trials while the gateway view was null. It refutes
sole-gateway-observation correspondence on that **single-host harness**,
not on a new VM. Conversely a faster x86 KVM pair cannot by itself establish
absence of shared physical cache, time, management and hypervisor paths.

**Not yet authorized/performed:** a new architecture port, image lock,
guest build, VM provision, owner-approved protocol amendment, 64-lifetime
replay, new side-channel trial or independent attestation.
