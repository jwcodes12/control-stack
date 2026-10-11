# Tier 8 self-review (Claude Opus 5.5)

Adversarial pass over Tier 8 claims: vacuity, scanned-versus-tested artifact, overclaims.

- **Demo static stage verifies saved fixture IRs, not fresh scans.** The 44 fixtures are
  DECLARED/static inputs. A fresh scan happens only in the live stage, on the exact Compose
  files started there (`run_remediated.py` captures the daemon inventory, rescans and
  kernel-verifies before the workload). DEMO.md and the quickstart say so.
- **The live stage tests usefulness, not denial.** It runs only the two repaired
  configurations with honest work. Denial evidence remains the archived Tier 2 runs. No
  table calls the demo a bypass test.
- **Fresh clone was not a fully fresh environment.** The clone came from GitHub, but Lean
  dependencies were linked from this box's pinned prebuilt packages (no network). The
  download path is exercised only by the CI kernel job.
- **Skips cannot pass.** Demo exit 3 on any SKIPPED stage; the release workflow asserts the
  live stages are SKIPPED and exit is 3; the live job is `if: false` on GitHub runners.
- **Schemas are partly loose.** `snapshot` in the bundle schema is an unconstrained object;
  `mode` in plan host actions allows string or integer. The golden tests pin exact bytes.
- **Golden files carry host-specific absolute paths** inherited from the fixture IRs
  (Sol's clone path). They are deterministic data, not observations of this host.
- **Held-out contamination** (Tier 6) was not visible in earlier headlines; the review
  packet now reports the pre-fix score as the uncontaminated one.
- **Trusted-path review is a model review.** It found no violation of the conclusion but
  three unstated premises (delegation, indeterminate timeouts/HALT liveness, CAP_SETUID).
  Each is now stated in the claim with evidence where possible (`deployment/sink_audit.py`
  over all archives; `runs/tier8/capability-check` on the actual imported image). Trusted
  code was not changed; fixes are queued as T9 because archive replays pin current sources.
- **Sink audit special case.** `.gitkeep` is excluded by exact name only; it is the
  repository placeholder for empty archived sinks. The writable-sink archives prove the
  audit detects an unattributed file.
- **Exact-head CI** for Tier 8 is recorded in END-STATE.md, not asserted here.

No known false CONDITIONAL. Tier 8 does not change verifier rules, fixtures or frozen evidence.
