# Deployment verifier quickstart (scoped R2, local-file slice)

This is a **scoped beta** for one deployment class: the Linux local-file receiver, two
untrusted agents, separate reviewer/approver, exact one-use approval and one shared budget.
It never says *safe* or *assured*. The best verdict is **CONDITIONAL**, which means: no
configuration bypass found in the extracted model, the Lean kernel accepted the same
finite facts, and two premises remain unproved (faithful extraction, protocol refinement).
Precise claim: [DEPLOYMENT-CLAIM-v0.md](DEPLOYMENT-CLAIM-v0.md).

## One command

```
git clone --branch sol/r2-tier8 https://github.com/jwcodes12/control-stack.git && cd control-stack
lake exe cache get            # or link an existing pinned .lake/packages; no other installs
python3 tools/cstack.py demo --output /tmp/cstack-demo
```

`cstack demo` runs, in order, and writes everything under the new output directory:

| Stage | What it does | Needs |
|---|---|---|
| verify fixtures + Lean kernel | 51 example deployments (the frozen legacy corpus of 1 clean + 43 misconfigured, plus the hardened profile's 1 clean + 6 misconfigured) through the Python verifier and the Lean kernel; compares with `examples/compose-two-agent/expected.json` and `examples/compose-two-agent-hardened/expected.json`; reports any false CONDITIONAL | Python 3.12+, Lean (pinned toolchain) |
| plan remediation | read-only RFC 6902 patch for two misconfigured deployments; checks it yields the reference clean profile | Python |
| live remediated containers | builds an offline image, starts each **repaired** deployment with Docker Compose, captures the daemon inventory, fresh-scans it, kernel-verifies it, runs an honest two-agent task, reconciles sink bytes against the broker database, removes every `cstack-r2-` resource | Docker + Compose, passwordless `sudo`, the offline rootfs |
| independent sink-side check | separate checker replays the saved raw inventories and reconciles sink files with SQLite | Python |

Defensive scope: no bypass is launched live. Bypass outcomes are archived Tier 2
measurements (`deployment/runs/tier2/containers-final`).

`--static-only` runs the first two stages and reports the live ones as SKIPPED.

Supported profile (hardened, from the source generation that introduced it): both agent
services carry `security_opt: ["no-new-privileges:true"]` and `cap_drop: ["ALL"]`, the
broker runs without delegation (no `--allow-delegation`), and the runtime inventory reports
both settings. A deployment without them is UNASSURED (UNKNOWN edge), and `cstack plan`
adds them. Reference files: `examples/compose-two-agent-hardened/`.

## Exit codes (stable)

| Command | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| `cstack scan` | IR written | — | invalid input / pin mismatch | — |
| `cstack verify` | CONDITIONAL | UNASSURED (including a skipped `--lean`) | invalid input | — |
| `cstack plan` | proposal written | — | invalid input / output would overwrite an input | — |
| `cstack report` | rendered | — | invalid bundle (including any non-CONDITIONAL/UNASSURED verdict) | — |
| `cstack demo` | every stage PASS | a stage FAILED | usage (e.g. output exists) | no failure, but a stage SKIPPED — **never a pass** |

Errors go to stderr prefixed `cstack:`. Machine output is canonical JSON (sorted keys,
two-space indent). Schemas: `security_ir/schema-v0.1.json` (IR),
`deployment/schemas/bundle-v0.1.json`, `plan-v0.1.json`, `demo-v0.1.json`. Golden
outputs: `deployment/golden/`, checked by `tools/test_deployment_release.py`.

## Step by step

```
cstack scan  compose.json --runtime runtime.json --sha256 <compose sha256> --output ir.json
cstack verify ir.json --lean --output bundle.json      # without --lean: always UNASSURED
cstack plan   compose.json --runtime runtime.json --ir ir.json --output plan.json
cstack report bundle.json --output report.md
```

`runtime.json` is a selected inventory (UIDs, image IDs, mounts, networks, environment
variable **names**). For live deployments collect it with `deployment/collect_docker.py`;
it is Docker-daemon-reported, not independent attestation.

## Supported platforms and versions

Tested end to end only on this host:

| Component | Version |
|---|---|
| OS / kernel | Oracle Linux Server 9.8, 6.12.0 UEK, aarch64 |
| LSMs | lockdown, capability, yama, selinux (Enforcing), bpf, ima, evm. **No Landlock.** |
| Docker / Compose | 29.8.0 / v5.5.1, default seccomp, namespaces and UID mapping |
| Python (host) | 3.14.8; CI uses 3.12 for static stages |
| Lean | `leanprover/lean4:v4.34.0` with the pinned `lake-manifest.json` |
| Image | offline `docker import` of `/var/tmp/sc01-vm-assets/build-root` (content-addressed image ID pinned per run) |

GitHub-hosted Ubuntu 24.04 runners run the static, Lean and archived-evidence stages
(`.github/workflows/deployment-release.yml`). They cannot run the live stage (no offline
rootfs); it is reported SKIPPED. Nothing else (other distributions, x86_64 live runs,
rootless Docker, Podman, Kubernetes, macOS, Windows, WASI) has been tested — do not infer
support.

## Claim ladder

| Rung | Meaning here | Examples |
|---|---|---|
| **Proven in model** | Lean kernel theorem over the finite IR or the abstract protocol; standard axioms only | `Accepted` instance per IR; `deployment_broker_safe`; `accepted_path_safety_monotone`; one-use and shared-budget contracts |
| **Tested at boundary** | Observed on real containers on this host, read from sink-side state and the broker database, not from the gate's own log | 7 Tier 2 cases (clean, 2 configuration bypasses observed, replay/overspend/egress blocked, crash/HALT, UID drift); 2 Tier 5 repaired configs; demo live stage |
| **Assumed** | Stated premise, not proved or tested universally | faithful extraction; protocol refinement (`sinkEffects = model.bank`); TCB components below; Docker inventory truthful |
| **Measured** | Finite empirical counts with their denominators | 51 fixtures (44 legacy + 7 hardened); 26+250 differential cases; 520 monotone additions; 25 sealed held-out cases; 9 archived episodes |

## Threat model (short)

Attacker: controls either or both agent programs and their requests; may replay, race,
substitute payloads, request forbidden roles, attempt direct writes or alternate deputies.
Cannot: change the pinned snapshot, trusted code, role assignment, private database, sink
directory, kernel, or approver inputs. Out of scope: semantic harmlessness of approved
content, covert host changes after capture, a malicious Docker daemon, whole-host
containment. Full text: [DEPLOYMENT-CLAIM-v0.md](DEPLOYMENT-CLAIM-v0.md).

## Trusted computing base

Linux kernel, filesystem DAC/UID enforcement and Docker's namespaces/seccomp; Docker
daemon and its inventory reports; the host operator and mount/credential custody; Python
and its libraries; Unix-socket `SO_PEERCRED` server; `trusted_stack/controller.py`
(broker), SQLite durability and locking; `trusted_stack/outbox_receiver.py`; trusted
reviewer/approver/admin operators; SHA-256; trusted clock; the collector, scanner,
validator, verifier and Lean serializer in this repository; the Lean kernel and pinned
libraries. **None has had independent review** (gate G1, open).

## Result lifetime

A verdict expires on any change to mounts or aliases, UIDs or role mappings, credentials,
inherited descriptors, image digests, network topology, runtime inventory, launcher,
broker or receiver hashes, policy, budget, or storage/clock configuration. Re-collect and
re-verify. No continuous drift monitoring is provided.

## Changing trusted code (versioned pins)

Archived runs record the SHA-256 of the broker, receiver and container entry they ran.
Those digests stay checkable because every generation of the pinned files is kept in
`deployment/pinned-sources/<generation>/` (append-only, `.pysrc` suffix; `deployment/pins.py`).
A recorded digest is accepted only if the current file or a vaulted file **with that
path** hashes to it; the vault is trusted by bytes, never by name.

To change `trusted_stack/*.py` or `tools/deployment_container_entry.py`:

1. edit the code;
2. `python3 deployment/pins.py snapshot <new-generation>` (refuses an unchanged tree);
3. regenerate the current-reference artifacts (`tools/build_deployment_fixtures.py`, then
   `tools/build_deployment_golden.py`) so their pins name the new code. The frozen legacy
   corpus (`examples/compose-two-agent`, `security_ir/fixtures`) is bound to archived
   evidence at generation `r2-v0` and does not change;
4. `python3 deployment/pins.py vault-templates`: the hardened templates embed the pins, so
   their new digests are content-addressed in `deployment/pinned-templates/` (archived
   remediation plans name a template only by digest);
5. `python3 tools/test_deployment_pins.py` and the archive replays must still pass.

A pin set recorded by an archive must belong to **one** generation (the evidence checkers
reject a mixture), and the checkers refuse to run under `python -O`.

Archive replays may use any vaulted generation. A **fresh** scan, collection, or live run
requires the current tree, so evidence from an older generation never certifies new code.
