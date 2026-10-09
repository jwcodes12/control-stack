# Structural integration verification — 2026-10-08 (GitHub CI)

**Validation run:** [GitHub Actions #37870787641](https://github.com/jwcodes12/control-stack/actions/runs/37870787641), conclusion **SUCCESS**, on isolated branch `lean-validation-run-20261008`; initial source under test is a descendant of hardening head `beccb760`. The workflow changed only its own CI configuration and regenerated deterministic `THEOREM-REGISTRY.md` / `.json`. These generated files were copied byte-for-byte to `structure-merge-20261008-gpt6-finish` in commit `b8fa84c`. No experimental evidence was generated.

## Actual CI results

| Gate | Observed result | Scope |
|---|---|---|
| Lean pinned-toolchain compilation | **PASS** | `lake build ControlStack` completed twice (GitHub logged 3,743 jobs then 3,742 replay jobs) |
| Standard-axiom inspection | **PASS for printed reports** | 8 reports from all scenario claim elaborations, each involving only `propext`, `Classical.choice`, `Quot.sound`; the first build log also included 446 such standard-only reports, no `sorryAx` |
| Every `scenarios/SC-XX/claim.lean` | **PASS** | All 28 individually elaborated using `lake env lean`; this checks syntax/Lean queries, not whether a draft has a theorem |
| Theorem registry and scenario status index | **PASS** | `python3 tools/build_registry.py --check`, `python3 tools/build_status.py --check`; 860 lexical declaration records; 850 remain `SOURCE_ONLY` |
| Scenario metadata static lint | **PASS** | All 28 manifests and checked digests, scoped obligations and registered source references accepted; all unresolved cases remain blocked |
| Adversarial checker unit tests | **PASS** | `python3 -m unittest tools.test_check_scenarios`: 18 cases, including tamper/missing-axis/false-promotion fixtures |
| Certifier unit tests | **PASS** | `python3 tools/test_ctrlcert.py`: 4 cases |
| SC-01 original checker, steps 1–4 | **PASS** | Lean case/support chain, hashes, Python/Lean gateway differential test and frozen 64/64 historical single-host usefulness receipt |
| SC-01 original checker, step 5 | **EXPECTED HOST-BOUND FAILURE** | The historical cache receipt includes an OpenSSL host binding that cannot match a new ephemeral GitHub runner. No frozen receipt or source hash was regenerated. The acceptance script verified the host-bound error message and did not classify this as a new side-channel experiment |
| New VM trial / honest-task recovery / attestation | **NOT RUN** | The saved frozen VM usefulness failure and single-host shared-cache refutation stand independently of this build |

The first validation attempt [#37866728862](https://github.com/jwcodes12/control-stack/actions/runs/37866728862) built Lean successfully but failed on stale generated registry files. Those files were deterministically regenerated and committed, and the full replay above passed.

## Integrity and limits

The hardening merge retains exactly **28 manifests / 28 Lean claim files, three CONDITIONAL and 25 DRAFT**. All have separate per-assumption proof/evidence/applicability/usefulness fields and six named scope-review obligations. The static checker refuses self-declared `RUNTIME_VALIDATED`, `MET_RECORDED`, or `SUPPORTED` statuses, duplicate JSON keys, missing axes and source/digest mismatches.

The comparison against source integration head `f526fee` verified **all 82 checked protected blobs unchanged**, including root `PREREG-*.md`, historical results/VM receipts, assurance files and the original scenario-A workflow. Three editable B drafts were relocated with **identical original Git blob hashes** into `prereg/`, without altering immutable historical preregs.

This result is a **clean structural and machine-checking acceptance**, not a completed safety case. A lexically indexed declaration is not proof of intended statement fidelity. Nonstandard-axiom absence in *printed results* is not an independent review of every statement. SC-01's original single-host cache side certificate was refuted; the frozen VM QEMU TCG 0.25 s usefulness gate previously failed 0/64 baseline and 0/64 mediated. Hardware isolation, independent lineage/observation attestation, broad runtime correspondence and human protocol approval remain unresolved.

## Reproduce

```sh
git switch structure-merge-20261008
bash tools/verify_structure_merge.sh
```

The script does not modify experimental receipts, fixed deadlines or preregistrations. On a new host, it accepts precisely the expected step-5 historic OpenSSL host-binding failure **only after steps 1–4 pass**, and fails for any unrelated error. See the CI logs for the executed proof/test replay; do not treat the presence of the script as a substitute for running it.

## Follow-up, 2026-10-08 — Independent branch and expanded Lean replay

[Run #37877045361](https://github.com/jwcodes12/control-stack/actions/runs/37877045361) passed `ControlStack.HaltLiveness` kernel elaboration (standard-only axiom reports), full 3,744-job merged build, 28 scenario claim files, 18 metadata tests, 4 certifier tests, 865-record registry drift and original SC-01 phases 1–4. No evidence was rewritten. The single-host cache receipt still does not validate as a fresh host-bound receipt. The independent A/B/C exact-commit results, including C's original stale registry defect, are in [comparison.md](comparison.md). Source-level theorem scope annotations were expanded by 34; the remaining 821 unknown adversary scopes are not automatically promoted.

## Final exact-source acceptance, 2026-10-08

**[GitHub Actions run #37877960110](https://github.com/jwcodes12/control-stack/actions/runs/37877960110) — SUCCESS.** A read-only checkout of integrated **source commit `b4493224d6758449c2cea1bc65dc257fe6886393`** ran pinned Lean 4.34.0: `lake build ControlStack` **3,744 jobs PASS**; unchanged acceptance script rebuilt 3,743 jobs and elaborated **28/28 scenario claim files** with **eight standard-only printed axiom reports**, **18 scenario mutation tests** and **four certifier tests** all PASS. The 865-entry theorem registry and scenario index both passed drift checks. SC-01's original checker reached all first four checks; step five failed only on the expected historic-host OpenSSL cache receipt binding and the narrow acceptance exception matched. No receipt or preregistration was rewritten. The later work-branch commits modify only documentation and add a manual-only workflow; the checked Lean, checker and registry sources are unchanged.
