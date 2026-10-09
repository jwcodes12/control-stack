# Structure-merge comparison — 2026-10-08

**Baseline:** `origin/main` at `18c18590c5aa86b6f12def6d7416788eae232425`. Compared GitHub branch trees and inspected each branch's checker/tests/generators and sampled schemas. The first source audit ran where local shell networking and Lean were unavailable; the **subsequent independent GitHub-hosted CI reran each original A/B/C branch on its pinned original SHA**. The results below distinguish static tests, generators, individual claim replays and full Lean compilation. New working branch: `structure-merge-20261008`; no merge to main.

| Branch | Changed-file delta vs main | Scenario folders | Theorem-backed/current bundles | Static safeguards | Executed tests/build |
|---|---:|---:|---:|---|---|
| A `scenario-architecture-20261008` | 132 | 28 | 4 active (SC-01,03,13,27), rest draft | 4 axes, path containment, duplicate JSON-key rejection, runner allowlist, metadata promotion denied | **PASS** lint, 8 tests, generator drift, Lean build (3,715 jobs) |
| B `scenario-bundles-static-checker-20261008` | 205 | 28 | 3 conditional (SC-01,03,13), 25 draft | 3 statuses per named premise, source/evidence SHA-256, blocks self-deployment assurance; **not** proof replay | **PASS** 7 tests, static lint, Lean build (3,715 jobs), 28 individual Lean claims |
| C `scenario-backbone-20261008` | 89 | 28 | 4 active case bundles, 24 draft-only | 6 applicability axes, required proof/evidence digests, can optionally replay Lean axiom queries, independent assurance refused | **PASS** checker, 7 tests, 4 active Lean axiom replays, Lean build (3,715 jobs); **FAIL** original registry drift |

## What the checkers actually enforce

**A.** `tools/check_scenario.py --all --lint` parses a single `scenario.json` per case, validates schema, reference paths, required per-axis assumptions (proof/evidence/applicability/usefulness), disallows arbitrary runners, rejects approved status, and avoids untrusted manifest-defined shell commands. `--verify` only hashes listed evidence and invokes the *fixed* SC-01 legacy tool when allowlisted; it does not re-check general Lean claims and **always returns code 3** even when there is no refutation, so it cannot meet a precise “exit 3 iff refuted” contract. `tests/test_scenarios.py` covers missing axis, invented verification, path traversal, runner injection and duplicate JSON keys. The two A workflows check scenario lint/tests and index drift; both are adapted to the chosen checker below. This was independently replayed on the original SHA; see the CI matrix below.

**B.** `tools/check_scenarios.py` validates existence of six bundle artifacts, source/evidence hashes (allows expressly `UNBOUND` evidence), all three statuses on each named assumption, failure accounting, and restricts manifest status to DRAFT/CONDITIONAL/FAILED. It reports `RECORDED_NOT_RECHECKED`, never elevates self-recorded `KERNEL_CHECK_RECORDED` to a new machine check, and never infers `deployment_assured`. Gaps found: original B checker did **not** require referenced theorem names in its generated registry or in `claim.lean`, does not run Lean, and does not prove provenance of evidence origin; several declared artifacts are intentionally unbound or failed. The merge adds registry/source/`#check` linkage but it remains lexical until Lean replay. `tools/test_check_scenarios.py` has mutations for assumptions, digests, traversal, failed receipts and refusal to clear a conditional case. No actual test result was observed.

**C.** `tools/check_scenario.py --all` validates C-specific `scenario.yaml` (JSON subset), manifest, six axes (threat coverage, runtime correspondence, environment boundary, lifetime/composition, usefulness, independent review), pinned source/evidence hashes, paths, explicit premises, negative tests and no auto-assurance. Optional `--verify-proofs` runs Lean to replay `#print axioms` with standard axiom names. `--require-assured` always refuses self-promotion. `tools/test_check_scenario.py` has mutation controls for removed axes, unsupported promotion, hash changes and traversal. But only SC-01,03,13,27 have full active manifests; other 24 are `draft.md` only. `Core/Leakage.lean` is just an import facade, **not** the reviewed main file, and C's generic `GateComposition`/ `PolicyTamper` are model-level lemmas, not runtime refinements. No actual test result was observed.

## Decision and retained design

- Select **B's `claim.lean` plus `manifest.json` tree**, one `scenarios/` directory and one `tools/check_scenarios.py`. Retain all 28 cases while not mislabelling 25 drafts as verified. Keep A's two workflows with commands rewritten for B+merged registry; do not retain A's competing checker/status files.
- Add C's Lean folders, `PolicyTamper`, `GateComposition`, adversary taxonomy and `prereg/` *templates*. Relocate the six reviewed main source files into these folders, rather than replacing them with C's old import facade. Keep thin legacy-path modules; ensure root Lean module imports all new compilation targets.
- Use exactly one generated theorem registry at repo root with Markdown and JSON. C's lexical generator reports `UNKNOWN` where no validated annotation exists, rather than inventing a strategy model or theorem proof. Merge adds a manifest→registry→source name check. It is **not** a Lean symbol resolver.
- Preserve original `PREREG-*.md`, original run evidence/receipts and the original SC-01 step-5 host-bound OpenSSL comparison. Future experiment templates under `prereg/` are clearly distinct from frozen preregistrations. No mathematical novelty claim.
- Retain **ROADMAP.md** as the sole human status entry point; `scenarios/INDEX.md` is a generated scenario tally, not a second narrative status file.

## Verification commands (run on pinned networked GitHub CI)

```sh
lake exe cache get
lake build ControlStack
python3 tools/check_sc01_case.py
python3 tools/test_ctrlcert.py
python3 -m unittest tools.test_check_scenarios
python3 tools/check_scenarios.py
python3 tools/build_registry.py --check
python3 tools/build_status.py --check
lake env lean scenarios/SC-01/claim.lean
lake env lean scenarios/SC-03/claim.lean
lake env lean scenarios/SC-13/claim.lean
```

**Interpreting failures:** SC-01 steps 1–4 must pass; step 5's host-bound `/usr/bin/openssl` hash failure is expected on a fresh machine *only when it is the sole cause*. Any other error is a regression. Check generator drift, source registry links and mutation failure exit before signoff. Explicitly inspect the Lean axiom output (standard axioms only) and grep for `sorry`/unjustified `axiom` in new proof code. The listed merged-branch gates were executed in successful CI [#37870787641](https://github.com/jwcodes12/control-stack/actions/runs/37870787641) and expanded-theory CI [#37877045361](https://github.com/jwcodes12/control-stack/actions/runs/37877045361). The separately pinned A/B/C evaluation is documented below.

## Independent replay on exact original commits (2026-10-08)

| Source | Pinned original commit | Runner and checks | Result |
|---|---|---|---|
| **A** | `cbec4db5ea670e8a4585175b3b2f9d420d3ef3be` | [CI #37876990441](https://github.com/jwcodes12/control-stack/actions/runs/37876990441): `check_scenario.py --all --lint` (28/28), 8 unit/mutation tests, `lake build ControlStack` (3,715 jobs). [Extra #37877591251](https://github.com/jwcodes12/control-stack/actions/runs/37877591251): both `build_status.py --check` and `build_theorem_registry.py --check`. | **PASS** |
| **B** | `fe330a55c1dc667b9e1e5877b3ad4383cd047690` | [CI #37876990441](https://github.com/jwcodes12/control-stack/actions/runs/37876990441): `check_scenarios.py` (28/28), 7 mutation tests, `lake build ControlStack` (3,715 jobs). [Extra #37877591251](https://github.com/jwcodes12/control-stack/actions/runs/37877591251): 28/28 original `claim.lean` individually elaborated; only standard printed axioms and no `sorryAx`. | **PASS** |
| **C** | `e78a580412b5cfb2b96382e13ffb6ccda5f978f1` | [CI #37877138209](https://github.com/jwcodes12/control-stack/actions/runs/37877138209): four active case checkers, `lake build ControlStack` (3,715 jobs), and four active case Lean axiom replays **PASS**. [Extra #37877802725](https://github.com/jwcodes12/control-stack/actions/runs/37877802725): 7 mutations via correct direct-script invocation and refusal of self-assurance **PASS**. | **PASS except original registry drift** |

### Original C failures and treatment

- C's `python3 tools/build_registry.py --check` returns **nonzero**: `THEOREM-REGISTRY.md is stale` at the pinned original source commit. Regeneration followed by `--check` passed in a *disposable runner checkout*; no change was pushed to C. The merge's generated 865-entry theorem registry was checked in [#37877591251](https://github.com/jwcodes12/control-stack/actions/runs/37877591251) and is current.
- The first exploratory C run [#37876990441](https://github.com/jwcodes12/control-stack/actions/runs/37876990441) used `python3 -m unittest tools.test_check_scenario`, which fails with `ModuleNotFoundError: check_scenario` because the original test script imports a sibling by filename. The correct `python3 tools/test_check_scenario.py` invocation passed **7 tests** in [#37877802725](https://github.com/jwcodes12/control-stack/actions/runs/37877802725). This was an audit-command error, not an underlying test failure.
- C's original root module does **not** import `PolicyTamper.lean` or `GateComposition.lean`; a successful C original root build alone does not cover them. The two files are Git-blob-identical in the merged branch, where `ControlStack.lean` imports them and its full Lean build passed. C's original standalone source requires no speculative proof rewrite.

### Final integration and frozen records

The selected merged branch has **one** `scenarios/` tree and checker, 28 manifests/claims, **three conditional and 25 draft** scenarios, and one generated registry (865 declarations: 855 SOURCE_ONLY; 821 adversary UNKNOWN). Thirty-four candidate source-level scope annotations were added without an assurance promotion or independent statement-fidelity certification.

[Expanded Lean acceptance #37877045361](https://github.com/jwcodes12/control-stack/actions/runs/37877045361) passed all 28 claim elaborations, 18 merged checker tests, 4 certifier tests, 865-record index drift and SC-01 unchanged steps 1–4. `ControlStack/HaltLiveness.lean` now contains four additional standard-axiom-only theorems concerning explicit trusted HALT delivery and its necessity witness. No actual scheduler fairness or OS-mediated halt property was attested.

All original `PREREG-*.md`, scenario experiment receipts and VM receipts remain **byte-identical to main**. The SC-01 assurance manifest has only two source SHA-256 bindings updated, for relocated `ControlStack/Leakage.lean` and `ControlStack/Necessity.lean` compatibility facades; its claim, assumptions, evidence references and all historical receipts remain unchanged. These source-binding changes are necessary for the unchanged SC-01 checker steps 1–4 to pass. CI commits on disposable execution branches were needed to trigger Actions, but only `[skip ci]` commits were pushed to the work branch.


## Final exact-source acceptance, 2026-10-08

**[GitHub Actions run #37877960110](https://github.com/jwcodes12/control-stack/actions/runs/37877960110) — SUCCESS.** A read-only checkout of integrated **source commit `b4493224d6758449c2cea1bc65dc257fe6886393`** ran pinned Lean 4.34.0: `lake build ControlStack` **3,744 jobs PASS**; unchanged acceptance script rebuilt 3,743 jobs and elaborated **28/28 scenario claim files** with **eight standard-only printed axiom reports**, **18 scenario mutation tests** and **four certifier tests** all PASS. The 865-entry theorem registry and scenario index both passed drift checks. SC-01's original checker reached all first four checks; step five failed only on the expected historic-host OpenSSL cache receipt binding and the narrow acceptance exception matched. No receipt or preregistration was rewritten. The later work-branch commits modify only documentation and add a manual-only workflow; the checked Lean, checker and registry sources are unchanged.

## Branch file inventory (changed paths relative to baseline)

### scenario-architecture-20261008 (132 changed paths; ahead 5, behind 3)

- `added` `.github/workflows/generated-assurance-indexes.yml`
- `added` `.github/workflows/scenario-metadata.yml`
- `modified` `README.md`
- `modified` `ROADMAP.md`
- `added` `scenarios/README.md`
- `added` `scenarios/SC-01/claim.md`
- `added` `scenarios/SC-01/correspondence.md`
- `added` `scenarios/SC-01/prereg/DEADLINE-AMENDMENT.md`
- `added` `scenarios/SC-01/prereg/LIFETIME-INDEPENDENCE.md`
- `added` `scenarios/SC-01/prereg/TWO-INSTANCE-SIDE-PROBE.md`
- `added` `scenarios/SC-01/result.md`
- `added` `scenarios/SC-01/scenario.json`
- `added` `scenarios/SC-01/tests/README.md`
- `added` `scenarios/SC-02/claim.md`
- `added` `scenarios/SC-02/correspondence.md`
- `added` `scenarios/SC-02/result.md`
- `added` `scenarios/SC-02/scenario.json`
- `added` `scenarios/SC-03/claim.md`
- `added` `scenarios/SC-03/correspondence.md`
- `added` `scenarios/SC-03/result.md`
- `added` `scenarios/SC-03/scenario.json`
- `added` `scenarios/SC-03/tests/README.md`
- `added` `scenarios/SC-04/claim.md`
- `added` `scenarios/SC-04/correspondence.md`
- `added` `scenarios/SC-04/result.md`
- `added` `scenarios/SC-04/scenario.json`
- `added` `scenarios/SC-05/claim.md`
- `added` `scenarios/SC-05/correspondence.md`
- `added` `scenarios/SC-05/result.md`
- `added` `scenarios/SC-05/scenario.json`
- `added` `scenarios/SC-06/claim.md`
- `added` `scenarios/SC-06/correspondence.md`
- `added` `scenarios/SC-06/result.md`
- `added` `scenarios/SC-06/scenario.json`
- `added` `scenarios/SC-07/claim.md`
- `added` `scenarios/SC-07/correspondence.md`
- `added` `scenarios/SC-07/result.md`
- `added` `scenarios/SC-07/scenario.json`
- `added` `scenarios/SC-08/claim.md`
- `added` `scenarios/SC-08/correspondence.md`
- `added` `scenarios/SC-08/result.md`
- `added` `scenarios/SC-08/scenario.json`
- `added` `scenarios/SC-09/claim.md`
- `added` `scenarios/SC-09/correspondence.md`
- `added` `scenarios/SC-09/result.md`
- `added` `scenarios/SC-09/scenario.json`
- `added` `scenarios/SC-10/claim.md`
- `added` `scenarios/SC-10/correspondence.md`
- `added` `scenarios/SC-10/result.md`
- `added` `scenarios/SC-10/scenario.json`
- `added` `scenarios/SC-11/claim.md`
- `added` `scenarios/SC-11/correspondence.md`
- `added` `scenarios/SC-11/result.md`
- `added` `scenarios/SC-11/scenario.json`
- `added` `scenarios/SC-12/claim.md`
- `added` `scenarios/SC-12/correspondence.md`
- `added` `scenarios/SC-12/result.md`
- `added` `scenarios/SC-12/scenario.json`
- `added` `scenarios/SC-13/claim.md`
- `added` `scenarios/SC-13/correspondence.md`
- `added` `scenarios/SC-13/result.md`
- `added` `scenarios/SC-13/scenario.json`
- `added` `scenarios/SC-13/tests/README.md`
- `added` `scenarios/SC-14/claim.md`
- `added` `scenarios/SC-14/correspondence.md`
- `added` `scenarios/SC-14/result.md`
- `added` `scenarios/SC-14/scenario.json`
- `added` `scenarios/SC-15/claim.md`
- `added` `scenarios/SC-15/correspondence.md`
- `added` `scenarios/SC-15/result.md`
- `added` `scenarios/SC-15/scenario.json`
- `added` `scenarios/SC-16/claim.md`
- `added` `scenarios/SC-16/correspondence.md`
- `added` `scenarios/SC-16/result.md`
- `added` `scenarios/SC-16/scenario.json`
- `added` `scenarios/SC-17/claim.md`
- `added` `scenarios/SC-17/correspondence.md`
- `added` `scenarios/SC-17/result.md`
- `added` `scenarios/SC-17/scenario.json`
- `added` `scenarios/SC-18/claim.md`
- `added` `scenarios/SC-18/correspondence.md`
- `added` `scenarios/SC-18/result.md`
- `added` `scenarios/SC-18/scenario.json`
- `added` `scenarios/SC-19/claim.md`
- `added` `scenarios/SC-19/correspondence.md`
- `added` `scenarios/SC-19/result.md`
- `added` `scenarios/SC-19/scenario.json`
- `added` `scenarios/SC-20/claim.md`
- `added` `scenarios/SC-20/correspondence.md`
- `added` `scenarios/SC-20/result.md`
- `added` `scenarios/SC-20/scenario.json`
- `added` `scenarios/SC-21/claim.md`
- `added` `scenarios/SC-21/correspondence.md`
- `added` `scenarios/SC-21/result.md`
- `added` `scenarios/SC-21/scenario.json`
- `added` `scenarios/SC-22/claim.md`
- `added` `scenarios/SC-22/correspondence.md`
- `added` `scenarios/SC-22/result.md`
- `added` `scenarios/SC-22/scenario.json`
- `added` `scenarios/SC-23/claim.md`
- `added` `scenarios/SC-23/correspondence.md`
- `added` `scenarios/SC-23/result.md`
- `added` `scenarios/SC-23/scenario.json`
- `added` `scenarios/SC-24/claim.md`
- `added` `scenarios/SC-24/correspondence.md`
- `added` `scenarios/SC-24/result.md`
- `added` `scenarios/SC-24/scenario.json`
- `added` `scenarios/SC-25/claim.md`
- `added` `scenarios/SC-25/correspondence.md`
- `added` `scenarios/SC-25/result.md`
- `added` `scenarios/SC-25/scenario.json`
- `added` `scenarios/SC-26/claim.md`
- `added` `scenarios/SC-26/correspondence.md`
- `added` `scenarios/SC-26/result.md`
- `added` `scenarios/SC-26/scenario.json`
- `added` `scenarios/SC-27/claim.md`
- `added` `scenarios/SC-27/correspondence.md`
- `added` `scenarios/SC-27/result.md`
- `added` `scenarios/SC-27/scenario.json`
- `added` `scenarios/SC-27/tests/README.md`
- `added` `scenarios/SC-28/claim.md`
- `added` `scenarios/SC-28/correspondence.md`
- `added` `scenarios/SC-28/result.md`
- `added` `scenarios/SC-28/scenario.json`
- `added` `scenarios/STATUS.md`
- `added` `scenarios/THEOREM-REGISTRY.md`
- `added` `scenarios/THEORY-BACKLOG.md`
- `added` `scenarios/theorem-registry.json`
- `added` `tests/test_scenarios.py`
- `added` `tools/build_status.py`
- `added` `tools/build_theorem_registry.py`
- `added` `tools/check_scenario.py`

### scenario-bundles-static-checker-20261008 (205 changed paths; ahead 2, behind 3)

- `modified` `README.md`
- `added` `scenarios/README.md`
- `added` `scenarios/SC-01/claim.lean`
- `added` `scenarios/SC-01/correspondence.md`
- `added` `scenarios/SC-01/manifest.json`
- `added` `scenarios/SC-01/policy.json`
- `added` `scenarios/SC-01/prereg/deadline-amendment-DRAFT.md`
- `added` `scenarios/SC-01/prereg/lifetime-independence-DRAFT.md`
- `added` `scenarios/SC-01/prereg/two-instance-side-channel-DRAFT.md`
- `added` `scenarios/SC-01/result.md`
- `added` `scenarios/SC-01/tests/README.md`
- `added` `scenarios/SC-01/threat.md`
- `added` `scenarios/SC-02/claim.lean`
- `added` `scenarios/SC-02/correspondence.md`
- `added` `scenarios/SC-02/manifest.json`
- `added` `scenarios/SC-02/policy.json`
- `added` `scenarios/SC-02/result.md`
- `added` `scenarios/SC-02/tests/README.md`
- `added` `scenarios/SC-02/threat.md`
- `added` `scenarios/SC-03/claim.lean`
- `added` `scenarios/SC-03/correspondence.md`
- `added` `scenarios/SC-03/manifest.json`
- `added` `scenarios/SC-03/policy.json`
- `added` `scenarios/SC-03/result.md`
- `added` `scenarios/SC-03/tests/README.md`
- `added` `scenarios/SC-03/threat.md`
- `added` `scenarios/SC-04/claim.lean`
- `added` `scenarios/SC-04/correspondence.md`
- `added` `scenarios/SC-04/manifest.json`
- `added` `scenarios/SC-04/policy.json`
- `added` `scenarios/SC-04/result.md`
- `added` `scenarios/SC-04/tests/README.md`
- `added` `scenarios/SC-04/threat.md`
- `added` `scenarios/SC-05/claim.lean`
- `added` `scenarios/SC-05/correspondence.md`
- `added` `scenarios/SC-05/manifest.json`
- `added` `scenarios/SC-05/policy.json`
- `added` `scenarios/SC-05/result.md`
- `added` `scenarios/SC-05/tests/README.md`
- `added` `scenarios/SC-05/threat.md`
- `added` `scenarios/SC-06/claim.lean`
- `added` `scenarios/SC-06/correspondence.md`
- `added` `scenarios/SC-06/manifest.json`
- `added` `scenarios/SC-06/policy.json`
- `added` `scenarios/SC-06/result.md`
- `added` `scenarios/SC-06/tests/README.md`
- `added` `scenarios/SC-06/threat.md`
- `added` `scenarios/SC-07/claim.lean`
- `added` `scenarios/SC-07/correspondence.md`
- `added` `scenarios/SC-07/manifest.json`
- `added` `scenarios/SC-07/policy.json`
- `added` `scenarios/SC-07/result.md`
- `added` `scenarios/SC-07/tests/README.md`
- `added` `scenarios/SC-07/threat.md`
- `added` `scenarios/SC-08/claim.lean`
- `added` `scenarios/SC-08/correspondence.md`
- `added` `scenarios/SC-08/manifest.json`
- `added` `scenarios/SC-08/policy.json`
- `added` `scenarios/SC-08/result.md`
- `added` `scenarios/SC-08/tests/README.md`
- `added` `scenarios/SC-08/threat.md`
- `added` `scenarios/SC-09/claim.lean`
- `added` `scenarios/SC-09/correspondence.md`
- `added` `scenarios/SC-09/manifest.json`
- `added` `scenarios/SC-09/policy.json`
- `added` `scenarios/SC-09/result.md`
- `added` `scenarios/SC-09/tests/README.md`
- `added` `scenarios/SC-09/threat.md`
- `added` `scenarios/SC-10/claim.lean`
- `added` `scenarios/SC-10/correspondence.md`
- `added` `scenarios/SC-10/manifest.json`
- `added` `scenarios/SC-10/policy.json`
- `added` `scenarios/SC-10/result.md`
- `added` `scenarios/SC-10/tests/README.md`
- `added` `scenarios/SC-10/threat.md`
- `added` `scenarios/SC-11/claim.lean`
- `added` `scenarios/SC-11/correspondence.md`
- `added` `scenarios/SC-11/manifest.json`
- `added` `scenarios/SC-11/policy.json`
- `added` `scenarios/SC-11/result.md`
- `added` `scenarios/SC-11/tests/README.md`
- `added` `scenarios/SC-11/threat.md`
- `added` `scenarios/SC-12/claim.lean`
- `added` `scenarios/SC-12/correspondence.md`
- `added` `scenarios/SC-12/manifest.json`
- `added` `scenarios/SC-12/policy.json`
- `added` `scenarios/SC-12/result.md`
- `added` `scenarios/SC-12/tests/README.md`
- `added` `scenarios/SC-12/threat.md`
- `added` `scenarios/SC-13/claim.lean`
- `added` `scenarios/SC-13/correspondence.md`
- `added` `scenarios/SC-13/manifest.json`
- `added` `scenarios/SC-13/policy.json`
- `added` `scenarios/SC-13/result.md`
- `added` `scenarios/SC-13/tests/README.md`
- `added` `scenarios/SC-13/threat.md`
- `added` `scenarios/SC-14/claim.lean`
- `added` `scenarios/SC-14/correspondence.md`
- `added` `scenarios/SC-14/manifest.json`
- `added` `scenarios/SC-14/policy.json`
- `added` `scenarios/SC-14/result.md`
- `added` `scenarios/SC-14/tests/README.md`
- `added` `scenarios/SC-14/threat.md`
- `added` `scenarios/SC-15/claim.lean`
- `added` `scenarios/SC-15/correspondence.md`
- `added` `scenarios/SC-15/manifest.json`
- `added` `scenarios/SC-15/policy.json`
- `added` `scenarios/SC-15/result.md`
- `added` `scenarios/SC-15/tests/README.md`
- `added` `scenarios/SC-15/threat.md`
- `added` `scenarios/SC-16/claim.lean`
- `added` `scenarios/SC-16/correspondence.md`
- `added` `scenarios/SC-16/manifest.json`
- `added` `scenarios/SC-16/policy.json`
- `added` `scenarios/SC-16/result.md`
- `added` `scenarios/SC-16/tests/README.md`
- `added` `scenarios/SC-16/threat.md`
- `added` `scenarios/SC-17/claim.lean`
- `added` `scenarios/SC-17/correspondence.md`
- `added` `scenarios/SC-17/manifest.json`
- `added` `scenarios/SC-17/policy.json`
- `added` `scenarios/SC-17/result.md`
- `added` `scenarios/SC-17/tests/README.md`
- `added` `scenarios/SC-17/threat.md`
- `added` `scenarios/SC-18/claim.lean`
- `added` `scenarios/SC-18/correspondence.md`
- `added` `scenarios/SC-18/manifest.json`
- `added` `scenarios/SC-18/policy.json`
- `added` `scenarios/SC-18/result.md`
- `added` `scenarios/SC-18/tests/README.md`
- `added` `scenarios/SC-18/threat.md`
- `added` `scenarios/SC-19/claim.lean`
- `added` `scenarios/SC-19/correspondence.md`
- `added` `scenarios/SC-19/manifest.json`
- `added` `scenarios/SC-19/policy.json`
- `added` `scenarios/SC-19/result.md`
- `added` `scenarios/SC-19/tests/README.md`
- `added` `scenarios/SC-19/threat.md`
- `added` `scenarios/SC-20/claim.lean`
- `added` `scenarios/SC-20/correspondence.md`
- `added` `scenarios/SC-20/manifest.json`
- `added` `scenarios/SC-20/policy.json`
- `added` `scenarios/SC-20/result.md`
- `added` `scenarios/SC-20/tests/README.md`
- `added` `scenarios/SC-20/threat.md`
- `added` `scenarios/SC-21/claim.lean`
- `added` `scenarios/SC-21/correspondence.md`
- `added` `scenarios/SC-21/manifest.json`
- `added` `scenarios/SC-21/policy.json`
- `added` `scenarios/SC-21/result.md`
- `added` `scenarios/SC-21/tests/README.md`
- `added` `scenarios/SC-21/threat.md`
- `added` `scenarios/SC-22/claim.lean`
- `added` `scenarios/SC-22/correspondence.md`
- `added` `scenarios/SC-22/manifest.json`
- `added` `scenarios/SC-22/policy.json`
- `added` `scenarios/SC-22/result.md`
- `added` `scenarios/SC-22/tests/README.md`
- `added` `scenarios/SC-22/threat.md`
- `added` `scenarios/SC-23/claim.lean`
- `added` `scenarios/SC-23/correspondence.md`
- `added` `scenarios/SC-23/manifest.json`
- `added` `scenarios/SC-23/policy.json`
- `added` `scenarios/SC-23/result.md`
- `added` `scenarios/SC-23/tests/README.md`
- `added` `scenarios/SC-23/threat.md`
- `added` `scenarios/SC-24/claim.lean`
- `added` `scenarios/SC-24/correspondence.md`
- `added` `scenarios/SC-24/manifest.json`
- `added` `scenarios/SC-24/policy.json`
- `added` `scenarios/SC-24/result.md`
- `added` `scenarios/SC-24/tests/README.md`
- `added` `scenarios/SC-24/threat.md`
- `added` `scenarios/SC-25/claim.lean`
- `added` `scenarios/SC-25/correspondence.md`
- `added` `scenarios/SC-25/manifest.json`
- `added` `scenarios/SC-25/policy.json`
- `added` `scenarios/SC-25/result.md`
- `added` `scenarios/SC-25/tests/README.md`
- `added` `scenarios/SC-25/threat.md`
- `added` `scenarios/SC-26/claim.lean`
- `added` `scenarios/SC-26/correspondence.md`
- `added` `scenarios/SC-26/manifest.json`
- `added` `scenarios/SC-26/policy.json`
- `added` `scenarios/SC-26/result.md`
- `added` `scenarios/SC-26/tests/README.md`
- `added` `scenarios/SC-26/threat.md`
- `added` `scenarios/SC-27/claim.lean`
- `added` `scenarios/SC-27/correspondence.md`
- `added` `scenarios/SC-27/manifest.json`
- `added` `scenarios/SC-27/policy.json`
- `added` `scenarios/SC-27/result.md`
- `added` `scenarios/SC-27/tests/README.md`
- `added` `scenarios/SC-27/threat.md`
- `added` `scenarios/SC-28/claim.lean`
- `added` `scenarios/SC-28/correspondence.md`
- `added` `scenarios/SC-28/manifest.json`
- `added` `scenarios/SC-28/policy.json`
- `added` `scenarios/SC-28/result.md`
- `added` `scenarios/SC-28/tests/README.md`
- `added` `scenarios/SC-28/threat.md`
- `added` `scenarios/THEOREM-REGISTRY.md`
- `added` `tools/check_scenarios.py`
- `added` `tools/test_check_scenarios.py`
- `added` `tools/theorem_registry.py`

### scenario-backbone-20261008 (89 changed paths; ahead 3, behind 3)

- `added` `ADVERSARY-CLASSES.md`
- `added` `ControlStack/Core/Leakage.lean`
- `added` `ControlStack/Core/Probability.lean`
- `added` `ControlStack/Core/TemporalGate.lean`
- `added` `ControlStack/Families/F1/Capability.lean`
- `added` `ControlStack/Families/F2/Observations.lean`
- `added` `ControlStack/Families/F3/Temporal.lean`
- `added` `ControlStack/Families/F4/Integrity.lean`
- `added` `ControlStack/Families/F5/Leases.lean`
- `added` `ControlStack/Families/F6/Probabilistic.lean`
- `added` `ControlStack/Families/F7/Approvals.lean`
- `added` `ControlStack/Families/F8/Composition.lean`
- `added` `ControlStack/GateComposition.lean`
- `added` `ControlStack/PolicyTamper.lean`
- `added` `ControlStack/Scenarios/SC01.lean`
- `added` `ControlStack/Scenarios/SC03.lean`
- `added` `ControlStack/Scenarios/SC13.lean`
- `added` `ControlStack/Scenarios/SC27.lean`
- `added` `ControlStack/Witnesses/CovertNoGo.lean`
- `modified` `README.md`
- `added` `STATUS.md`
- `added` `THEOREM-REGISTRY.md`
- `added` `prereg/LIFETIME-INDEPENDENCE-TEMPLATE.md`
- `added` `prereg/SC01-DEADLINE-AMENDMENT-TEMPLATE.md`
- `added` `prereg/TWO-INSTANCE-SIDE-CHANNEL-PROBE-TEMPLATE.md`
- `added` `registry/annotations.json`
- `added` `scenarios/README.md`
- `added` `scenarios/SC-01/claim.lean`
- `added` `scenarios/SC-01/correspondence.md`
- `added` `scenarios/SC-01/manifest.json`
- `added` `scenarios/SC-01/policy.json`
- `added` `scenarios/SC-01/result.md`
- `added` `scenarios/SC-01/scenario.yaml`
- `added` `scenarios/SC-01/tests/README.md`
- `added` `scenarios/SC-01/tests/test_static_case.py`
- `added` `scenarios/SC-02/draft.md`
- `added` `scenarios/SC-03/claim.lean`
- `added` `scenarios/SC-03/correspondence.md`
- `added` `scenarios/SC-03/manifest.json`
- `added` `scenarios/SC-03/policy.json`
- `added` `scenarios/SC-03/result.md`
- `added` `scenarios/SC-03/scenario.yaml`
- `added` `scenarios/SC-03/tests/README.md`
- `added` `scenarios/SC-03/tests/test_static_case.py`
- `added` `scenarios/SC-04/draft.md`
- `added` `scenarios/SC-05/draft.md`
- `added` `scenarios/SC-06/draft.md`
- `added` `scenarios/SC-07/draft.md`
- `added` `scenarios/SC-08/draft.md`
- `added` `scenarios/SC-09/draft.md`
- `added` `scenarios/SC-10/draft.md`
- `added` `scenarios/SC-11/draft.md`
- `added` `scenarios/SC-12/draft.md`
- `added` `scenarios/SC-13/claim.lean`
- `added` `scenarios/SC-13/correspondence.md`
- `added` `scenarios/SC-13/manifest.json`
- `added` `scenarios/SC-13/policy.json`
- `added` `scenarios/SC-13/result.md`
- `added` `scenarios/SC-13/scenario.yaml`
- `added` `scenarios/SC-13/tests/README.md`
- `added` `scenarios/SC-13/tests/test_static_case.py`
- `added` `scenarios/SC-14/draft.md`
- `added` `scenarios/SC-15/draft.md`
- `added` `scenarios/SC-16/draft.md`
- `added` `scenarios/SC-17/draft.md`
- `added` `scenarios/SC-18/draft.md`
- `added` `scenarios/SC-19/draft.md`
- `added` `scenarios/SC-20/draft.md`
- `added` `scenarios/SC-21/draft.md`
- `added` `scenarios/SC-22/draft.md`
- `added` `scenarios/SC-23/draft.md`
- `added` `scenarios/SC-24/draft.md`
- `added` `scenarios/SC-25/draft.md`
- `added` `scenarios/SC-26/draft.md`
- `added` `scenarios/SC-27/claim.lean`
- `added` `scenarios/SC-27/correspondence.md`
- `added` `scenarios/SC-27/manifest.json`
- `added` `scenarios/SC-27/policy.json`
- `added` `scenarios/SC-27/result.md`
- `added` `scenarios/SC-27/scenario.yaml`
- `added` `scenarios/SC-27/tests/README.md`
- `added` `scenarios/SC-27/tests/test_static_case.py`
- `added` `scenarios/SC-28/draft.md`
- `added` `theory/OPEN-OBLIGATIONS.md`
- `added` `theory/SHARED-STATE-AND-TAMPER.md`
- `added` `tools/build_registry.py`
- `added` `tools/build_status.py`
- `added` `tools/check_scenario.py`
- `added` `tools/test_check_scenario.py`

## SC-01 source-hash rebind in this work branch

After relocating the reviewed declarations, the unchanged historical SC-01 verifier still reads and kernel-queries its original `ControlStack/Leakage.lean` and `ControlStack/Necessity.lean` paths. Those paths now import the new definitions **and repeat exactly the theorem axiom queries named in the original assurance manifest**. The two corresponding SHA-256 bindings in `assurance/sc01-safety-case.json` are updated to the new *facade source bytes*. This is a versioned binding change in the assurance metadata, **not** a change to any historical experiment, cache receipt, preregistration, measured result or theorem statement. The unchanged verifier must still be executed to demonstrate steps 1–4 actually pass; it was not run in the current network-restricted shell.

## Lexical completeness repair

An additional read-only sweep of **102 Lean source files** found three declarations omitted by C's original lexical scanner: `System.run_nil`, `System.run_cons` (both inline `@[simp]` declarations) and `MultiStep.V_zero`. It also truncated the dotted declaration names `Spec.trace_safe` and `NoAgentEffects.agent_trace_inert`. The generator and single registry were corrected: **852** named theorem/lemma declarations indexed. This remains a lexical inventory and does not resolve namespace identity or guarantee that every declaration type/elaboration form is covered. A new regression test exercises the additional syntax. Neither the modified scanner nor that test was executed in this shell.
