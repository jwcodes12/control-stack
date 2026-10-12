# Self-hosted fast runner (`oci-fast-1`)

Purpose: fast feedback (about a minute for a small change) from `.github/workflows/fast-lean.yml`. It is **not** the authoritative gate: the
GitHub-hosted workflows still run from a clean machine. A result from this runner is only as trustworthy as this box.

## Where it runs and why that is acceptable
On the owner's Oracle free-tier VM, as the unprivileged user `ghrunner`: no sudo, not in the `docker` group, no access to `/home/opc`.
Only the repository's owner can open PRs (private repo). PR code from agents still executes here, so the box must hold no secrets
`ghrunner` can read. Jobs needing sudo or docker (live containers, the scanner test) are not run here.

## Layout
- `/opt/actions-runner` and `/opt/actions-runner-2` (runner v2.338.0, checksum-verified against GitHub's published digest), services
  `actions.runner.jwcodes12-control-stack.oci-fast-{1,2}.service`, limits in `…service.d/limits.conf`: nice 10, CPU 80% each, memory 6 GB each, no new privileges.
- `/opt/ci-shared/lean-v4.34.0` and `/opt/ci-shared/packages`: read-only bind mounts (also in `/etc/fstab`) of the pinned Lean toolchain and the built Mathlib
  from the owner's home. The runner user cannot read the home directory itself.
- `/opt/ci-shared/bin/python3` -> Linuxbrew Python 3.14 (the hosted gate uses 3.12; the suites pass on both).
- `/var/lib/ghrunner/lake-build-cache-oci-fast-N`: one persistent `.lake/build` per runner process (two runners, `oci-fast-1` and `-2`; separate
  caches because two concurrent `lake build`s must not share one directory). Lake keys on content hashes, so stale
  entries from other branches are safe, but a hostile PR could poison it: delete it if in doubt.
- Disk is the constraint (root volume near full). The workflow refuses to run with under 1.5 GB free.

## Operate
- Status: `gh api repos/jwcodes12/control-stack/actions/runners`; `systemctl status actions.runner.*`.
- Stop: `sudo systemctl disable --now actions.runner.jwcodes12-control-stack.oci-fast-1.service`.
- Remove: `cd /opt/actions-runner && sudo -u ghrunner ./config.sh remove --token <removal token>`, delete `/opt/actions-runner`, `/var/lib/ghrunner`, the
  two `/etc/fstab` lines and `/opt/ci-shared`, then `sudo userdel ghrunner`.
- Rebuild the shared Mathlib or bump the toolchain only together with `lean-toolchain` and the bind-mount source path.
