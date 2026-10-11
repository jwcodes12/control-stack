# END-STATE — deployment verifier, handoff `HANDOFF-SOL-TO-R2.md`

Date: 2026-10-11. Tiers 1–7 by Sol (GPT via Codex); Tier 8 by Claude Opus 5.5 after Sol's
thread hit its usage limit. Nothing merged; publication, tagging and merging are the owner's call.

## Reached level: scoped R2 (not R3, not R4)

All eleven section 7 gates are met for the claimed scope **except independent human review**,
which is G1 (`deployment/RELEASE-GATES.md`). Concretely:

- one command from a fresh clone: `python3 tools/cstack.py demo --output DIR` — PASS at
  beb396a, all four stages, 112 s (`deployment/runs/tier8/demo-fresh-clone-final`);
- zero known false CONDITIONALs (44/44 fixtures; 25 sealed held-out cases, zero false
  acceptances in every scoring phase);
- residual premises stated in `docs/DEPLOYMENT-CLAIM-v0.md`, including three found by the
  Tier 8 trusted-path review;
- every recorded failure listed in `deployment/REVIEW-PACKET-R2.md` section 4.

**What R2 does not mean:** no deployment is "assured"; CONDITIONAL rests on unproved
faithful extraction and protocol refinement; tested on one host (Oracle Linux 9.8, aarch64,
Docker 29.8, no Landlock); no LLM agent was ever run against it; only two live bypasses
were observed, both on deliberately misconfigured deployments.

## Not finished but grindable (no resource needed)

T9.1–T9.6, trusted-path hardening from the Tier 8 review: versioned source pins, delegation off,
server robustness (crash on malformed input, slow-sender stall, HALT retry), `no-new-privileges`
plus `cap_drop`, pending-file reaper, then re-run the non-bypass live cases. None of these
findings violates the claim's conclusion; all are stated as premises until fixed.
So the stop condition "every remaining task needs a resource" is **not yet** met.

## Queue

| Tier | Status |
|---|---|
| T1 harden #45 | 10/10 DONE |
| T2 real containers | 7/7 DONE |
| T3 scanner coverage | 6/6 DONE |
| T4 Lean | T4.1, T4.3, T4.5 DONE; **T4.2 BLOCKED** (literal monotonicity false: 3 kernel countermodels; safety-only monotonicity proved); **T4.4 BLOCKED** (concrete transcript replay failed 3 compile attempts) |
| T5 remediation | 3/3 DONE (defensive: only repaired configs run live) |
| T6 held-out | 3/3 DONE |
| T7 attribution | 4/4 DONE (defensive recast); original T7.2/T7.3 attack arms GATED |
| T8 release | 6/6 DONE |
| T9 hardening | 6 TODO |

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
SQLite, Python, broker/receiver, scanner/verifier/serializer, Lean); and, from the Tier 8
review: no delegation in covered runs (checked by `deployment/sink_audit.py`), timeouts
are indeterminate (retry approvals only with the same nonce), no HALT liveness, and agent
UIDs cannot regain CAP_SETUID (image evidence in `deployment/runs/tier8/capability-check`).

## Failures

All are in `deployment/REVIEW-PACKET-R2.md` section 4, with raw evidence under
`deployment/runs/tier*/`. Headline ones: two false CONDITIONALs in the original PR #45
(fixed in T1); T4.2 and T4.4 BLOCKED; held-out contamination; the `cyber_policy` stop that
forced the defensive-only scope.

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
| Tier 8 | sol/r2-tier8 | this commit | see the PR's checks (recorded after the run) |

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
