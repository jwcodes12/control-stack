# G5: host Landlock enabled, Landlock-dependent tests run (2026-10-13)

Before: `CONFIG_SECURITY_LANDLOCK=y` but `landlock` absent from `/sys/kernel/security/lsm`, so `landlock_create_ruleset` returned
ENOTSUP and the host-boundary tests never ran on this box. With the owner's go-ahead ("Yes, reboot now") the default kernel entry
(UEK 6.12.0-206, other entries untouched as fallback) got `lsm=lockdown,capability,yama,selinux,bpf,landlock,ima,evm`
(`grubby --update-kernel=DEFAULT --args=...`) and the box was rebooted. After boot: LSM list includes landlock, Landlock ABI 6
(`probe.txt`), SELinux still in the list, `post-boot-check` all ok, no failed units.

Run by the one-shot `g5-landlock-check.service` as root (files in this directory), plus two manual runs:
- `probe.txt`: `landlock_abi=6 libseccomp=present`, exit 0.
- `test_agent_confinement.txt` (root): OK, 1 skipped (`NO AGENT EVIDENCE: non-root test UID required`).
- `test_agent_confinement_nonroot.txt` (as `opc`, the case that really exercises the kernel): **3 of 3 OK**, including
  `test_host_denies_actual_writes_network_fork_and_metadata` and `test_cannot_fall_back_to_unconfined_execution`.
- `test_confined_effect_broker.txt`: PASS (real kernel-confined delegate, SO_PEERCRED, one shared budget, exactly one trusted file effect, replay/HALT negatives).
- `test_polyglot_broker.txt`: PASS. `test_trusted_stack_broker.txt`: PASS (21 peer-credential checks, 9 disconnected callers, 2 releases, 1 exact file effect).
- `boundary/`: `tools/run_deployment_boundary.py` (native cross-UID experiment, disposable UIDs 23700-23704, no accounts created) run under `/var/tmp` because
  UID 23700 cannot traverse `/home/opc`; result plus sink snapshots archived here.

Scope: one host (OL 9.8 aarch64, UEK 6.12.0-206). Landlock restricts filesystem writes, network (ABI >= 4), and the tests show the
launcher's rules deny actual writes, network, fork and metadata changes for the confined agent; it is not a claim about kernel
exploits, other hosts, or the Docker deployment (which uses namespaces and cap-drop, not this launcher). Not independent attestation; no human review.
