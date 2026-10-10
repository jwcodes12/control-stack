# COMPLETED.md — consolidated control-stack engineering handoff (2026-10-09)

**Repository:** `jwcodes12/control-stack` · **single PR:** [#39](https://github.com/jwcodes12/control-stack/pull/39) · **working branch:** `work/consolidated-control-stack-20261009`

**Scope and status:** repository-side reference implementations, finite model tests and an adversarial self-audit were added to the existing control-stack work. They are **not** claims of full deployment assurance, complete Lean-to-runtime refinement, cryptographically attested OS mediation, or independent expert review. All 28 scenario assurance claims remain **CONDITIONAL**; none is deployment assured. Merge only after the **latest PR-head SHA**, real workflow job steps, generated indexes, kernel runs, axiom checks and protected files are verified. Historical pass results from older SHAs must not be presented as a fresh green PR.

## P0 — integration, bounded differentials and statement fidelity

- **SC-06 / SC-08:** Prior mainline SC-06 approval-before-ingestion fix and one-use confirmation model are retained unchanged. The existing consolidated PR adds `reviews/sc06-issuer-controls/Controls.lean`, which exercises role identities, one-use approvals, wrong reader/tool, HALT and useful nonvacuous behavior. SC-08 sealed memfd negatives are added in `tools/test_sc08_sealed_script.py`, including actual kernel sealing flags and injected failure, with `sc08-sealed-script` CI. These are source and Linux-local controls, not proof of universal exec mediation.
- **SC-06/08/25 bounded Lean/Python model parity:** `tools/bounded_model_diff.py` independently computes expected transition results using Python shadow machines, then asks pinned Lean to check the same finite trace equations using `by decide`. It exhausts lengths 0–2 over declared operation alphabets and adds longer directed attack/honest causal chains. Outputs checked include approvals/effects/expired items/HALT; disagreement fails CI. See [scope](docs/BOUNDED-DIFFERENTIAL-SCOPE.md).
- **SC-26:** pre-existing `scenarios/SC-26/harness/lean_difftest.py -n 200` checks source-evaluated Lean model against the independent Python counterpart across seeded legal traces and negative-control check configurations. It is now part of the same dedicated CI. No independent bank/refinement guarantee is implied.
- **Adversarial fidelity:** [detailed self-audit](reviews/statement-fidelity-2026-10-09/consolidated-audit.md) distinguishes the literal theorem statements of `SC06OneUse.scoped_safe`, `SC08.sc08_safe`, `SC25.sc25_safe`, `SC26.sc26_safe`, F6 and F8 from stronger English or runtime claims. [Lean scope witnesses](reviews/statement-fidelity-2026-10-09/Counterexamples.lean) show SC-25's `halt_freezes` constrains the execution log, not all volatile state; SC-26's formal `legal` predicate imposes no approver-identity provenance. Independent human review remains explicitly open.

## P1 — trusted reference effect, F6/F8 and assurance premises

- **Real atomic SQLite effect, not external effect:** `trusted_stack/controller.py` creates `effect_records`, carrying the **exact reviewed artifact body, digest and destination**. `trusted_stack/server.py` admits an `effect_release` request under broker-derived `SO_PEERCRED`. Content append, one-use approval consumption, budget accounting and release record occur in one SQLite transaction. Replaying the nonce cannot produce another row, and a failed insert rolls back the whole operation. The broker intentionally **does not execute programs, perform network calls, transfer funds, or intercept other effect paths**. [Explicit trust boundary](docs/TRUSTED-EFFECT-BOUNDARY.md).
- **Reference effect regression:** `trusted_stack/test_effect_service.py` covers exact bytes, invalid identifiers, role rejection, injected database sink failure, transaction rollback, concurrent replay and HALT. The entire existing trusted-stack simulator, transition oracle and Linux peer-credential tests remain required.
- **F6:** [review-scoped candidate Lean file](reviews/family-strengthening/F6F8.lean) adds a sound intersection-of-misses bound and fully correlated monitor counterexample to naive multiplicative recall, plus a false-positive nonattack lemma. This does not assert positive empirical conditional recall or useful false-positive tolerance. Existing `EnsembleKernel.ensK_adaptive` is conditional on per-history law/recall.
- **F8:** the same Lean review file adds a quantified `shared_family_invariants` induction over all joint actions when every action preserves every constituent invariant. It does **not** prove this all-invariant premise for real OS/network/SC26 effects. The existing confused-deputy counterexample remains. Candidate proof sources were deliberately kept in `reviews/` rather than silently promoted as source-registry-assured mainline results.
- **Assurance priorities:** credentials (19 scenarios), honest usefulness (18), exclusive effect path (11), observation completeness and implementation correspondence are [mapped to evidence and outstanding gates](reviews/statement-fidelity-2026-10-09/consolidated-audit.md). Source-only UID/role checks and the SQLite effect narrow but do not discharge those deployment premises.

## P2 — regression, VM package, documentation

- **Adversarial regressions:** a new `reference-harness-dry-regression` CI runs SC-06/08/25 real-script reference harnesses with `--kind dry --reps 1` in disposable scratch, plus SC-26 model and bank controls (not experimental evidence; see [scope](docs/REFERENCE-DRY-REGRESSION.md)); retained SC-08 sealed-source Linux tests, SC-06 chronology controls, SC-25 approval/audit/timeout/amend/crash negative traces, SC-26 seeded full-state model parity and the trusted reference SQLite effects tests. No historical experiment was rerun or rewritten.
- **Reproducible VM source package:** `tools/package_vm_replay.py` deterministically creates a tar.gz with fixed timestamps/ownership containing the original SC-01 workload contract, image lock, VM recipes, controlled historical configuration and source-asset SHA-256 manifest; it **excludes images, credentials, historical receipts, preregistrations and frozen evidence**. `--verify` requires exact deterministic source match. `tools/test_vm_package.py` tests reproducibility and tampering. [VM package limitations and host steps](docs/VM-SOURCE-BUNDLE.md).
- **Generated indexes:** `THEOREM-REGISTRY.md`, `THEOREM-REGISTRY.json`, `LEAN-STATEMENTS-NORMAL-FORM.md`, `scenarios/INDEX.md` and assurance summaries are left governed by their source generators. New research proofs under `reviews/` intentionally do **not** change indexed mainline declarations; run the checks below and regenerate only when underlying indexed claims/manifests change. Existing 28-scenario CONDITIONAL status is not promoted. This file is the consolidated new work handoff, superseding only the outdated status narrative in the prior `COMPLETED.md`.

## Exact verification commands (repository root, fresh compatible environment)

```bash
git fetch origin main work/consolidated-control-stack-20261009
git checkout work/consolidated-control-stack-20261009
git rev-parse HEAD
git diff --name-status origin/main...HEAD
git diff --exit-code origin/main...HEAD -- ControlStack/EgressGate.lean
git diff --name-only origin/main...HEAD -- 'scenarios/*/evidence/**' 'gateway/vm/receipts/**' 'experiments/*/evidence/**'
# Any output to the protected-file diff command is a merge blocker.
python3 -m unittest discover -s trusted_stack -p 'test_*.py' -v
python3 -m unittest tools.test_vm_package -v
python3 tools/test_sc08_sealed_script.py -v
python3 tools/package_vm_replay.py --output /tmp/sc01-source-v1.tar.gz
python3 tools/package_vm_replay.py --verify /tmp/sc01-source-v1.tar.gz
python3 tools/build_registry.py --check
python3 tools/build_statement_catalog.py --check
python3 tools/build_status.py --check
python3 tools/check_scenarios.py
python3 tools/build_overview.py --check
python3 tools/portfolio_ledger.py --check
# Only with permitted Linux OS/root identities, in a disposable host/runner:
sudo -n python3 tools/test_trusted_stack_broker.py
# Pinned Lean (lean-toolchain + lake-manifest.json):
lake exe cache get
lake build ControlStack
lake env lean reviews/sc06-issuer-controls/Controls.lean
lake env lean reviews/family-strengthening/F6F8.lean
lake env lean reviews/statement-fidelity-2026-10-09/Counterexamples.lean
python3 tools/bounded_model_diff.py
python3 scenarios/SC-26/harness/lean_difftest.py -n 200
```

Inspect printed `#print axioms` of all modified/new claims, ensure no `sorryAx` or `sorry`/untrusted code-evaluation shortcut, inspect actual Actions job **steps**, and compare the completed results to the current exact PR HEAD SHA (not merely the latest green run on a former head). Check commit status and required branch rules through GitHub before a merge.

## CI provenance

[Consolidated PR checks](https://github.com/jwcodes12/control-stack/pull/39/checks) are the authoritative entry point. Dedicated required-or-expectable workflows include `bounded-model-differential`, `trusted-effect-reference`, `vm-source-bundle`, `sc06-oneuse-model`, `sc08-sealed-script`, `fast-checks`, `scenario-a-repair`, `egress-boundary`, `trusted-broker-disconnect`, `reference-harness-dry-regression`, and any enabled generated-index/Lean suites on current changes. Actions success on one source revision must not be generalized across later commits. `#print axioms` is **not** an independent statement-fidelity review.

## External blockers and exact remaining obligations

1. **Native SC-01 VM useful baseline (HARD BLOCKED on validated experiment/host):** previous QEMU TCG run [frozen receipt](gateway/vm/receipts/usefulness-20261008-linkfix.json) failed **0/64 baseline and 0/64 mediated** at the original 0.25s deadline. An authorized native KVM or separate-host environment with accessible hypervisor and corresponding host-specific source/image pins is needed; `gateway/vm/README.md` supplies full provisioning, isolation checks, negative fixture verification and `run_usefulness.py --config /path/to/config.json --output /new/receipt.json`. Reproduce **without editing** frozen inputs; only declare a new run after a separately approved protocol and safe, non-overwriting paths.
2. **Real effect mediation and model-to-runtime refinement (OPEN):** `effect_release` protects exactly one SQLite body append. Need a capability-isolated actual syscall/network/effect adapter, durable content-binding to the effect receiver, independent receiver idempotency, crisis/HALT interleaving semantics, crash/power-loss, same-UID bypass and trusted-deputy tests. Build an exact step relation to Lean and prove it; finite differential tests do not suffice.
3. **F6 positive imperfect monitoring (OPEN):** need an explicit conditional probability kernel supporting nonzero false positives, adaptive attacker feedback, shared blind spots and measured useful recall under every relevant history, plus real monitoring coverage. The co-miss counterexample prevents unjustified independence assumptions but cannot supply missing empirical premises.
4. **F8 actual multi-agent composition (OPEN):** prove global budgeting and release behavior for the *joint* runtime transition relation, including concurrent actors, delegated actions, bypasses and in-flight effects. The generic family invariant induction places this burden explicitly in `hJoint`, not in CI.
5. **Credential separation, observation and user usefulness (EXTERNAL):** independent OS trust anchor and credential custody, full side-channel observation accounting and valid held-out usefulness/monitor statistics remain unestablished.
6. **Independent reviewer (EXTERNAL):** appoint an unaffiliated reviewer to reproduce the pinned kernel/axiom outputs, inspect expanded statements, adversarial controls, all named premises and the runtime mapping. Reviewer must explicitly sign the exact source/hash/review version; this assistant self-audit does not count.

**Stop line:** A green model-only test, non-vacuous toy theorem, generated catalog, successful package checksum, or a SQLite atomic effect is not a deployment safety certificate. Do not mark any scenario DEPLOYMENT_ASSURED absent genuine external runtime and independently reviewed evidence.
