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
Docker 29.8, no Landlock); no LLM agent was ever run against it; only two live bypasses
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
| G2 | ControlArena / inspect_ai with real LLM agents: package installs, API budget, owner approval; attack arms also need cyber-permissive access. |
| G3 | OPA/Conftest, trivy, hadolint baselines: installs. |
| G4 | Kubernetes extractor on a real cluster: images or a cluster. |
| G5 | Host Landlock: kernel boot-parameter change (owner decision). |
| G6 | TPM/HSM key custody, GPU residue, multi-host: hardware. |
| G7 | HTTP sink with a real external destination: egress approval. |
| G8 | Windows, macOS, WASI backends. |
| G9 | Merge, tag, publish, outreach: owner. |
| T7.2/T7.3-original | New attack policies and the four-arm evaluation: cyber-permissive access. |
