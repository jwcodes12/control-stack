# G3: off-the-shelf baselines on the sealed held-out corpora (2026-10-13)

Run: `python3 tools/run_heldout_baselines.py --output deployment/runs/tier11/baselines` with `conftest 0.71.1` (OPA 1.21.1), `trivy 0.75.0`,
`hadolint 2.15.1` installed under `~/tools/bin` (arm64 release binaries, SHA-256 in `results.json`/`~/tools/dl/SHA256SUMS`) and the
`checkmarx/kics:latest` container (KICS v2.1.20, arm64, image id in `results.json`; removed afterwards). Raw per-case rows are in `results.json`.
A case is "rejected" if the tool reports any finding (KICS also at HIGH or above). A negative is a case whose sealed ground truth is not
`SAFE_IN_SUPPORTED_MODEL` (refuted or unknown configuration). Corpora: tier6 (25 cases: 5 safe, 20 negative) and tier10 (34: 8 safe, 26 negative).
Both corpora are **model-written** and sealed before scoring; neither author is an independent human.

| Baseline | tier6 negatives caught | tier6 safe over-rejected | tier10 negatives caught | tier10 safe over-rejected |
|---|---|---|---|---|
| hand-written Python rules (`deployment/rules_baseline.py`) | 2/20 | 0/5 | 0/26 | 0/8 |
| Conftest + OWASP-derived Rego (`deployment/baselines/owasp_compose.rego`) | 20/20 | **5/5** | 26/26 | **8/8** |
| KICS, any finding | 20/20 | **5/5** | 26/26 | **8/8** |
| KICS, HIGH or CRITICAL only | 0/20 | 0/5 | 2/26 | 0/8 |
| Trivy `config` | not applicable | | not applicable | |
| Hadolint | not applicable | | not applicable | |
| **This verifier** (archived, `deployment/runs/tier10/heldout/instantiated.json`, `tier6/heldout-after.json`) | 0 false CONDITIONAL of 20 | 0/5 | 0 false CONDITIONAL of 26 | 0/8 |

What this shows, and what it does not:
- The tools that read only declared Compose fields **do not discriminate**: configurations strict enough to reject every negative reject every supported
  case too (missing memory limits and read-only root filesystems are findings on the supported profile), and configurations lenient enough to keep the supported
  cases (KICS at HIGH, the Python rules) reject almost no negative. That is the expected gap: identity separation, the writer graph and runtime-inventory
  correspondence are not Compose fields.
- **Trivy** has no Compose scanner (`Detected config files num=0; Supported files for scanner(s) not found`), and **Hadolint** reads Dockerfiles, which no case has
  (the image is an offline rootfs import). They are reported as not applicable, not as zero findings.
- KICS validity checks: the runner refuses to report unless KICS scanned exactly one file per case (the first attempts scanned 0 files because KICS does not detect
  Compose in flow-style JSON, and mapped findings to the wrong directory; both were fixed and the zero-finding results discarded).
- The Conftest policy applies public OWASP Docker Security Cheat Sheet rules but was **written by this project's model**, so it is not an independent baseline,
  and different rule selections would move the numbers. KICS rules and Trivy/Hadolint are third-party.
- The verifier's rows use the "author-known-code hypothesis" instantiation for the trusted-source fact (without it every case is UNKNOWN, as in `raw.json`); they
  are the archived numbers, not re-run here. None of this is independent human evaluation (gate G1).
