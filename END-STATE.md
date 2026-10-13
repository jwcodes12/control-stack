# END-STATE — deployment verifier, handoff `HANDOFF-SOL-TO-R2.md`

Date: 2026-10-11. Tiers 1–7 by Sol (GPT via Codex); Tiers 8–9 by Claude Opus 5.5 after Sol's
thread hit its usage limit; Tier 10 (closure of the open engineering items, below) by Claude. Publication and tagging are the owner's call.

## Reached level: scoped R2 (not R3, not R4)

All eleven section 7 gates are met for the claimed scope **except independent human review**,
which is G1 (`deployment/RELEASE-GATES.md`). Concretely:

- one command from a fresh clone: `python3 tools/cstack.py demo --output DIR` — PASS at
  bacf4d6 (Tier 9), all four stages, 112 s (`deployment/runs/tier9/demo-fresh-clone`; the
  Tier 8 run is `deployment/runs/tier8/demo-fresh-clone-final`);
- zero known false CONDITIONALs (51/51 fixtures: 44 frozen legacy + 7 hardened-profile; 25 sealed held-out cases, zero false
  acceptances in every scoring phase);
- residual premises stated in `docs/DEPLOYMENT-CLAIM-v0.md`, including three found by the
  Tier 8 trusted-path review and the limits found by the Tier 9 review of the fixes;
- every recorded failure listed in `deployment/REVIEW-PACKET-R2.md` section 4.

**What R2 does not mean:** no deployment is "assured"; CONDITIONAL rests on unproved
faithful extraction and protocol refinement; tested on one host (Oracle Linux 9.8, aarch64,
Docker 29.8; Landlock was off until 2026-10-13, see G5 below); no LLM agent had been run against it at R2 (a tool-less agent and a scripted attack arm were added in Tier 11, see G2 and T7 below); only two live bypasses
were observed, both on deliberately misconfigured deployments.

## Tier 9: trusted-path hardening (done)

T9.1–T9.6 fixed what the Tier 8 review found, in source generations `r2-v1`..`r2-v4`
(`deployment/pinned-sources/`, `deployment/pins.py`): versioned pins so archived evidence
keeps replaying; delegation off by default and flagged by the scanner; a threaded broker with
a total read deadline, connection caps with slots reserved for trusted roles, catch-all
errors, HALT retry and restart-safe startup; agents must carry `no-new-privileges` and
`cap_drop: [ALL]` (v2 inventory, UNKNOWN edge, image file-capability scan with a positive
control); the receiver reaps pre-link `.pending-*` debris. Live evidence on the fixed code:
`deployment/runs/tier9/` (5 non-bypass cases + the demo; no bypass rerun).
An Opus 5.5 review of those fixes (`deployment/reviews/t9-hardening-review-opus.md`) found no
HIGH issue and three MEDIUM ones, all fixed; its open LOW items are stated in the claim.
**None of this has had independent human review.**

## Tier 10: the open engineering items (done, unreviewed by humans)

Closed in source generation `r2-v6` (details and limits in `docs/DEPLOYMENT-CLAIM-v0.md`, section "Tier 10"):
`Principals` refuses UID 0; the receiver refuses delegated releases by default; the evidence checkers bind one source
generation and refuse `python -O`; the image scan inventories the whole `/slice` tree and the interpreter start-up hooks; an
in-process HALT latch and a staging quota; `cstack plan` accepts a fresh scan's own IR; a start lock stops two brokers
removing each other's socket; `publish_effect` is pinned outside the claim by a test; the T4.4 replay uses the recorded broker
clock; live evidence for the five non-bypass cases and the demo on the final generation `r2-v7` (`deployment/runs/tier10/`: the five cases, `cstack demo` in the dev clone, and in a fresh clone at d42de1c, all PASS; the earlier `r2-v6` runs are in `gen-r2-v6/`); the Lean differential, contract-witness, monotonicity and transcript checkers pass;
a second held-out set (34 cases, blind `codex exec` author, hardened profile) that found **one false CONDITIONAL before
any fix** (an agent whose `SLICE_ROLE` is `broker`; fixed in the extractor, so the post-fix figures are contaminated).

## Still open

T4.2 (false as stated; the safety-only version is proved); independence of the held-out authors (all model-written); the
F6/F8 Lean candidates from #41 (their own gates are open); the base image outside `/slice` is trusted, not inspected;
receiver-side SQLite lock scheduling (mitigated in Tier 11 by a bounded retry, not fixed) and per-agent staging quotas (done in Tier 11, unit-tested only); one tested host. Everything else is in the gated table
below.

## Queue

| Tier | Status |
|---|---|
| T1 harden #45 | 10/10 DONE |
| T2 real containers | 7/7 DONE |
| T3 scanner coverage | 6/6 DONE |
| T4 Lean | T4.1, T4.3, T4.5 DONE; **T4.2 BLOCKED** (literal monotonicity false: 3 kernel countermodels; safety-only monotonicity proved); T4.4 DONE in Tier 9 (concrete replay of the archived clean transcript, generated Lean module, 3 falsifying mutants; the first three attempts failed on a `try a; b` parsing error) |
| T5 remediation | 3/3 DONE (defensive: only repaired configs run live) |
| T6 held-out | 3/3 DONE |
| T7 attribution | 4/4 DONE (defensive recast); original T7.2/T7.3 attack arms GATED |
| T8 release | 6/6 DONE |
| T9 hardening | 6/6 DONE (fixes unreviewed by humans) |
| T10 open items | DONE (see above; unreviewed by humans) |

Full table: `deployment/QUEUE.md`.

## Held-out and arms results

- **Held-out (T6):** 25 cases sealed by a sandboxed separate Codex author (5 supported,
  12 refuted, 8 unknown). Zero false model acceptances in every phase. Over-rejection of
  supported cases: raw 5/5, with the known-code hypothesis 2/5, and 0/5 after a mount-order
  fix that **those same cases prompted**, so 2/5 is the uncontaminated figure. 14/25
  UNKNOWN. A declaration-only rules baseline caught 2/20 negatives. Real OPA not run (G3).
- **Arms (T7):** no four-arm evaluation (GATED: the owner has no cyber-permissive model
  access). A retrospective, preregistered attribution of 9 archived episodes: 6 honest
  two-agent completions, 9 approved deliveries, 2 observed structural bypasses, 1
  unauthorized sink file, 5 evidence gaps; monitor not evaluated.

## Remaining premises

Faithful extraction; protocol refinement; the TCB (kernel, Docker daemon and its reports,
SQLite, Python, broker/receiver, scanner/verifier/serializer, Lean); the pin vault; for Tier 2–8
evidence (generation `r2-v0`) no delegation in covered runs (checked by
`deployment/sink_audit.py`), indeterminate timeouts (retry approvals only with the same
nonce), no HALT liveness, and agent UIDs cannot regain CAP_SETUID. On the hardened profile and
current source the delegation and CAP_SETUID premises are enforced (UNKNOWN edges, not
assumptions) and the slow-sender stall is fixed; database-busy timeouts remain indeterminate.

## Failures

All are in `deployment/REVIEW-PACKET-R2.md` section 4, with raw evidence under
`deployment/runs/tier*/`. Headline ones: two false CONDITIONALs in the original PR #45
(fixed in T1); T4.2 BLOCKED (false as stated), T4.4 blocked then finished; held-out contamination; the `cyber_policy` stop that
forced the defensive-only scope; in Tier 9 a `None` vs `[]` disagreement that only the real
Docker daemon exposed (`deployment/runs/tier9/attempt1-*`).

## PR chain (stacked drafts; merge in order)

| PR | Branch | Head | Exact-head CI |
|---|---|---|---|
| #45 | sol/deployment-slice-20261010 | 08ce227 | 25 pass, 2 skipped |
| #46 | sol/r2-tier2 | a94813c | 19 pass, 2 skipped |
| #47 | sol/r2-tier3 | 8c7ff72 | 19 pass, 2 skipped |
| #48 | sol/r2-tier4 | 3799130 | 24 pass, 2 skipped |
| #49 | sol/r2-tier5 | c0f5f45 | 18 pass, 3 skipped |
| #50 | sol/r2-tier6 | b263d0b | 18 pass, 3 skipped |
| #51 | sol/r2-tier7 | b59ec73 | 18 pass, 3 skipped (`deployment/runs/tier7/ci-receipt-b59ec73.json`) |
| #52 (Tier 8) | sol/r2-tier8 | 062b558 | 20 pass, 4 skipped by design (live-containers, linux-boundary, lean-vcvio) |
| Tier 9 | sol/r2-tier9 | this commit | see the PR's checks (recorded after the run) |

## Gated (needs a resource or owner decision)

| ID | Needs |
|---|---|
| G1 | Independent human review of statements, scanner semantics, enforcement and evidence handling (R3). Start with `deployment/REVIEW-PACKET-R2.md`. |
| G2 | **Partly done (2026-10-13, Tier 11):** a real LLM agent (tool-less `claude -p`, the model never touches the host) ran against the live hardened deployment: honest arm 3/3 delivered and independently verified; pressured arm 0/3 delivered, no effect without approval, **but the agents declined to try a bypass, so the boundary was not tested against an attempt** (`deployment/runs/tier11/llm-agent-eval/README.md`). Not done: ControlArena / inspect_ai itself (not installed), a larger sample, and attack arms (cyber-permissive access). |
| G3 | **Done as a measurement (2026-10-13, Tier 11):** Conftest/OPA with OWASP-derived Rego, KICS (public Compose rules) and the hand-written Python rules on both sealed held-out corpora; Trivy has no Compose scanner and Hadolint has no Dockerfile to read (not applicable). Strict baselines reject every negative and every supported case; lenient ones reject almost no negative (`deployment/runs/tier11/baselines/README.md`). The Rego is model-written; the corpora are model-authored. |
| G4 | **Partly done (2026-10-13): static extractor only.** `extractors/kubernetes/` translates a restricted `v1/List` of bare Pods plus one default-deny NetworkPolicy into the normalized profile the Compose extractor already reads (so authority rules stay in one place); `tools/test_kubernetes_extractor.py` (17 tests) shows the same authority graph as the Compose hardened reference and flags 14 single-fault mutants (privileged, hostNetwork, docker.sock hostPath, writable sink for an agent, missing cap-drop / allowPrivilegeEscalation, tag instead of digest, SA token, hostPID/IPC, secret/emptyDir volumes, valueFrom env, second container, root UID, weak or missing NetworkPolicy, unsupported kinds). **Not done:** any cluster run, a runtime collector (no `kubectl` capture; a runtime inventory has to be supplied), controllers/Services/RBAC/admission/CNI, and a held-out Kubernetes corpus. A real cluster needs privileged node containers or a VM on a host that is not this box (the Proxmox host is not authorised for that here). |
| G5 | **Done on this host (2026-10-13), with the owner's go-ahead:** `landlock` added to the kernel `lsm=` list and the box rebooted; Landlock ABI 6; `test_agent_confinement` 3/3 as non-root (it was skipped as root), `test_confined_effect_broker`, `test_polyglot_broker`, `test_trusted_stack_broker` and `tools/run_deployment_boundary.py` pass; evidence in `deployment/runs/tier11/g5-landlock/`. One host only; the Docker deployment does not use the Landlock launcher. The CI `linux-boundary` job on GitHub-hosted runners is still not this evidence. |
| G6 | **Open; owner to work out the approach (2026-10-13).** Facts about this box: a QEMU/KVM VM with no `/dev/tpm*`, no GPU, no `swtpm` (`tpm2-tools` is installed). So real key custody, GPU residue and multi-host cannot be tested here. Options: (a) real TPM 2.0 on another Linux machine you control; (b) a software TPM (`swtpm`) on this box, which exercises the sealing code path but is not custody and must be labelled so; (c) a cloud instance with vTPM or an HSM; GPU residue needs a GPU host; multi-host needs a second Linux host on the tailnet. Nothing in the deployment claim depends on any of these. |
| G7 | **Done as an outbox relay, deliberately outside the claim (2026-10-13):** `tools/http_relay.py` forwards receipt-verified sink files to a loopback HTTP destination (idempotency key, at-least-once on the wire, one stored copy at a key-honouring destination, relay-owned append-only acks, broker database untouched); demo on the archived live evidence in `deployment/runs/tier11/http-relay/`. **Not built:** an HTTP receiver inside the trusted slice (would need a new source generation, a network topology the scanner models, and a live re-run), TLS/authentication, any third-party destination. |
| G8 | **Closed by owner decision (2026-10-13): Linux only.** The deployment claim stays scoped to Linux (tested on one host: OL 9.8 aarch64, Docker 29.8, Landlock on since 2026-10-13); Windows, macOS and WASI backends are out of scope, not pending. Other Linux distributions and architectures (x86-64, Debian/Ubuntu, rootless Docker/Podman) are the in-scope way to widen host coverage and are not yet run. |
| Second Linux setup |**Partly done (2026-10-13):** the live suite ran on a second Linux setup, GitHub-hosted Ubuntu 24.04.5 x86-64 (kernel 6.17 azure, AppArmor, Landlock ABI 7, Docker 28.0.4): all five hardened cases agree and are CONDITIONAL, `check_container_run` PASS, the scripted attack arm 32/32 BLOCKED, Landlock-dependent tests pass (`deployment/runs/tier12-second-host/`, workflow `second-linux-host-live.yml`; failed attempts kept: a stock Ubuntu image is UNASSURED because of setid bits and `.pth` hooks). **Not done:** rootless Docker/Podman, SELinux on a non-Oracle distro, a non-cloud-VM host, older kernels, other architectures than aarch64 and x86-64 beyond these two hosts. |
| G9 | Merge, tag, publish, outreach: owner. |
| T7.2/T7.3-original | **Partly done (2026-10-13):** two Claude models (sonnet, opus; 2 trials each) acted as adaptive red-team attackers from inside the live hardened agent container (white-box source reading, enumeration, role-op probes): no file reached the sink, `release_log` clean in all four (`deployment/runs/tier11/llm-redteam-README.md`). Together with the 32-attempt scripted arm (`attack-arm/`) this tests the boundary against attempts. **Not done:** a stronger or longer-running attacker, a model without refusal training (cyber-permissive tier), more trials, ControlArena/inspect_ai itself, kernel/runtime exploits, other-role attacks. |
