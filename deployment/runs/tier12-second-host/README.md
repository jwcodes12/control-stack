# Second Linux setup: the live suite on GitHub-hosted Ubuntu 24.04 (x86-64, AppArmor), 2026-10-13

Workflow `.github/workflows/second-linux-host-live.yml` (run 38434279109 is `run3-ubuntu-24.04-x86_64/`; attempts 1 and 2 are kept).

| | primary host | second host |
|---|---|---|
| OS / kernel | Oracle Linux 9.8, UEK 6.12.0-206 | Ubuntu 24.04.5, 6.17.0-1022-azure |
| arch | aarch64 | x86-64 |
| LSMs | lockdown, capability, yama, **selinux**, bpf, landlock, ima, evm | lockdown, capability, landlock, yama, **apparmor**, ima, evm |
| Landlock ABI | 6 | 7 |
| Docker | 29.8 | 28.0.4 (Compose v2.38.2) |
| reference image | offline Oracle Linux rootfs | `ubuntu:24.04` + `python3`, setid bits and `.pth`/`sitecustomize` removed |

**Result on the second host (run 3).** Image build, fresh scan, Lean kernel check, live containers and independent reconciliation:
all five hardened cases (`clean`, `concurrent-cap1`, `crash-retry`, `halt-inflight`, `drift-uid`) predicted and observed as expected, every
configuration CONDITIONAL, `deployment/check_container_run.py` PASS; the scripted attack arm 32 of 32 BLOCKED (flood stopped at the
32 MiB per-agent share, honest agent-a completed afterwards); `test_agent_confinement` 3 of 3 as non-root, `test_confined_effect_broker`
PASS on that kernel with the Landlock probe at ABI 7. Rechecked from the archive by `tools/test_deployment_second_host.py`.

**What the failed attempts show.** Attempt 1 (stock Ubuntu image) and attempt 2 (setid bits cleared on files only) were UNASSURED, and the
scanner said why: `image-python-startup-hooks`, then `image-setuid-setgid-binaries` (it counts setgid DIRECTORIES too). That is the
scanner working on a general-purpose image, not a harness fault; a user deploying a stock distro image would get UNASSURED until
those are removed. The image preparation is part of the evidence: the claim covers the prepared image, not Ubuntu.

**Limits.** Still one claim, a different host: not a different architecture of the claim. Rootful Docker only (no rootless Docker or Podman),
no SELinux on this host (the `bind: selinux: z` option is ignored by Docker there), a GitHub-hosted VM (ephemeral, Azure kernel),
x86-64 and aarch64 only, no Debian-family host with a distro kernel older than 6.x, the Lean kernel check ran on this host's own build.
The attack-arm databases were slimmed (flood artifacts blanked; `SLIMMING.json`). Not independent attestation; no human review.
