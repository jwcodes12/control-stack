# Follow-up validation record — 2026-10-08

**Branch:** `structure-merge-20261008-gpt6-finish` (forked from concurrent integration head `f526fee07fdd2111e78e088986167deec68cd82c`). This report is about a **candidate**, not merged main, and not deployment assurance.

## Results actually observed

| Check | Result | What it means |
|---|---|---|
| GitHub tree inventory | **PASS (repository API)** | 28 scenario manifests, 28 `claim.lean` files; after moving editable drafts, zero scenario-local prereg files |
| Manifest structural audit | **PASS (repository API + JSON parsing)** | All 28 manifests contain the six complete conservative scope axes and per-premise usefulness status; SC-01 explicitly records shared-cache environment refutation and frozen VM usefulness failure |
| Existing named proof links | **PASS (source-link audit)** | Seven cited named theorems across SC-01/03/13 present in source registry and associated `claim.lean` query lines on integration baseline; these theorem identities were not edited in this hardening follow-up |
| Preregistrations | **PASS (byte hashes)** | Three B experiment drafts moved unchanged into `prereg/`; frozen root `PREREG-*.md` and historical evidence not modified |
| Shell acceptance runner | **PASS (syntax only)** | `bash -n` passed for `tools/verify_structure_merge.sh` in a disposable local copy |
| `lake build ControlStack`, 28 Lean claim replays | **NOT RUN** | Shell cannot resolve `github.com`, and Lean/Lake are unavailable; no valid clean-build or axiom result may be asserted |
| `tools/check_sc01_case.py` phases 1–5 | **NOT RUN** | No cloned checkout; the receipt's original-host OpenSSL SHA remains untouched |
| `tools/test_ctrlcert.py` and generic checker unittest suite | **NOT RUN** | No cloned checkout; additional regression test cases are checked in for a suitable host |
| Independent runtime correspondence / experimental usefulness | **NOT RUN** | Historical SC-01 refutations stand; new tests require a separate approved protocol |

## Checker design notes

The static `tools/check_scenarios.py` enforces six distinct scope review axes; per-premise *proof, evidence, applicability, and usefulness* records; uniqueness of JSON keys; names and file paths linked to the source-derived registry; and required evidence hashes, with explicit exception for historically unbound evidence. It disallows self-assignment of `SUPPORTED` scope, `RUNTIME_VALIDATED` evidence, or `MET_RECORDED` usefulness without a future separate attestation process. It **does not** run Lean or certify that a source theorem faithfully models a host process.

New negative-test fixtures cover missing usefulness and scope fields, attempted self-promotion, duplicate JSON keys, mismatched hash, missing registry reference, missing Lean claim query, path traversal and failed evidence. A positive result when running this checker will mean **metadata consistency only**, never an unconditional probability or deployment claim.

## Exact acceptance command on a networked checkout

```sh
git fetch --all
git switch structure-merge-20261008-gpt6-finish
bash tools/verify_structure_merge.sh
```

The runner performs the Lean cache/build, registry/status consistency checks, static and unit validation, all 28 `claim.lean` elaborations and standard-axiom report inspection, `test_ctrlcert`, then unchanged SC-01 case replay. It accepts the precise known new-host step-5 `shared file changed` error **only after steps 1–4 were reached**; unexpected failures exit nonzero. It changes no receipts, fixed experiment thresholds or preregistrations.

**Still open:** a real host replay, complete premise provenance and reviewer judgments, theorem classification beyond source-only UNKNOWN, and independent deployment correspondence. C's PolicyTamper/GateComposition remain narrow classical model statements. No novelty or operational safety claim.
