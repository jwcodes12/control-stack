# cstack demo

**PASS**  (exit 0)

Scoped R2 local-file two-agent slice. Verdicts never exceed CONDITIONAL; SKIPPED stages are not passes; no bypass is rerun live (defensive scope).

| Stage | Status | Detail |
|---|---|---|
| verify fixtures + Lean kernel | PASS | 44/44 fixtures match expected verdict and kernel result; false CONDITIONAL: none |
| plan remediation | PASS | read-only JSON Patch for writable-sink-mount, trusted-role-uid-collision yields the reference clean profile |
| live remediated containers | PASS | fresh daemon capture, fresh scan and kernel CONDITIONAL for trusted-role-uid-collision, writable-sink-mount; 4 honest deliveries; own resources removed |
| independent sink-side check | PASS | PASS: two remediated raw inventories, fresh observation replay, four honest deliveries, archived originals and cleanup; sink audit: every file is an attributed <id>.body, no delegation used |

Claim ladder: fixture verdicts and Lean acceptance are PROVEN_IN_MODEL for the extracted IR only; the live stage is TESTED_BOUNDARY on this host (Docker default seccomp/namespaces, no Landlock, daemon-reported inventory, not independent attestation); faithful extraction and protocol refinement remain ASSUMED; bypass outcomes are archived Tier 2 measurements.
