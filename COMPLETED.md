# Latest engineering continuation — delegated execution and empirical F6 (PR #40)

**Exact-status rule:** Claims below describe branch source changes, **not** a
deployment certificate. Inspect Actions jobs at the final HEAD before merge.
All 28 scenarios remain CONDITIONAL. No independent reviewer has signed
runtime correspondence or the policy premises.

- **F8 runtime authorization:** one-hop, immutable, nonce-specific delegation
  to an individually peer-authenticated agent UID. The grantor loses authority
  to spend that nonce; the delegate cannot redelegate or borrow another
  approval. Original lease owner and original global cap are charged within
  the same SQLite transaction. Revoking the grant (by grantor/admin) prevents
  later admissions *and* pending local-file publications; already durable
  publications cannot be undone. See
  [implementation scope](docs/DELEGATED-RELEASE-SCOPE.md) and
  `trusted_stack/test_delegation.py`. Existing databases need an offline
  trusted migration before the new schema is usable; this reference does not
  automatically migrate them.
- **F8 review-scoped Lean and correspondence testing:**
  `reviews/family-strengthening/DelegatedAdmission.lean` explicitly models
  one nonce, owner, delegate, immutable grant, revocation, one joint cap and
  absorbing HALT, with safety lemmas and a positive accepted delegated-release
  witness. `tools/delegated_lean_difftest.py` compares 72 actual SQLite
  event permutations and each corresponding projected finite state to
  kernel-checked Lean equations. These **bounded differential checks do NOT
  establish a universal Python/Lean semantics-preserving refinement** and
  cannot authenticate OS UIDs themselves.
- **F6 real public monitor data (exploratory):**
  `tools/redwood_f6_episode_report.py` reads the existing pinned LaStraj 2.0
  raw per-trajectory score vectors in
  `data/redwood-leaderboard/monitors.json`; one whole trajectory, not an
  individual action, is the sampling unit. It computes exact
  Clopper–Pearson one-sided upper bounds for attack misses and benign false
  alarms with a simultaneous adjustment across **all 19 monitor variants**
  (including the unscored variant). The report is always
  `EXPLORATORY_NOT_PREREGISTERED`, regardless of numeric outcome. A
  posthoc threshold and the small, history-unstratified, already-public
  dataset cannot discharge positive adaptive F6 monitoring. See
  [reproduction scope](docs/F6-TRAJECTORY-EMPIRICAL.md).
- **Preservation:** `ControlStack/EgressGate.lean`, historical evidence,
  preregistrations and VM receipts are unchanged by PR #40.

New verification on a pinned, provisioned Linux runner:
```sh
python3 -m unittest discover -s trusted_stack -p 'test_*.py' -v
python3 -m unittest tools.test_monitor_calibration tools.test_redwood_f6_episode_report -v
python3 tools/redwood_f6_episode_report.py --threshold 8 --output /tmp/redwood-f6-report-unique.json
lake env lean reviews/family-strengthening/DelegatedAdmission.lean
python3 tools/delegated_lean_difftest.py
python3 tools/joint_runtime_lean_difftest.py
```

**Undischarged:** universal OS/network/host effect capture, production-grade
capability confinement, power-loss and runtime-scheduler refinement,
actual Python-to-Lean proof for the whole delegated dispatcher, independently
precommitted adaptive F6 held-out trials, independent attested review and
native-hypervisor SC-01 usefulness. These require genuine environment and
evidence work; passing a source CI suite is insufficient.

---

# Control-stack remaining-work execution — PR #40

**Current continuation:** [single PR #40](https://github.com/jwcodes12/control-stack/pull/40) against main adds the next verified reference layers beyond merged PR #39. Source and CI claims here must be matched to PR #40's exact latest head; no deployment assurance is implied. The detailed previous handoff is retained below.

## Additional code shipped for verification

- `trusted_stack/outbox_receiver.py` publishes a committed reviewed artifact into a broker-owned **local filesystem** under a numeric release ID. Unlike the SQLite-only prototype, this emits real filesystem bytes; it is **not** a general network/OS action gate. The receiver does not expose an untrusted-agent RPC. Fail-closed checks include exact content/hash, dedicated trusted directory ownership/modes, symlink/hardlink prevention, no overwrite, fsync and persistent SQLite delivery acknowledgments. Crash between file publication and receipt commit is recovered only by comparing the durable existing bytes. A dedicated trusted-admin `python3 -m trusted_stack.deliver_cli` command dispatches without exposing a new agent RPC; delayed deliveries recheck lease revocation and both expiration deadlines. Final directory fsync also persists temporary hardlink cleanup. Concurrent HALT linearizes via SQLite `BEGIN IMMEDIATE`; previously published effects cannot be reversed.
- `trusted_stack/test_outbox_receiver.py` and `test_multi_actor_receiver.py` exercise fault injection, process restart, corruption, attack-shaped paths, concurrent independent agents, shared cap, duplicate replay and HALT. They are tests, not a universal semantic refinement.
- `reviews/family-strengthening/Remaining.lean` states explicit finite weighted per-history missed detection caps and concrete arbitrary-agent interleaving admission/absorbing-HALT theorems. The positive admission witness blocks trivial reject-all proofs. These are **review-scoped abstract models**, not certified OS implementation equivalence.
- `tools/monitor_calibration.py` computes held-out per-stratum one-sided miss/false-alarm Hoeffding upper bounds with a simultaneous union correction. Histories and thresholds must be frozen independently of evaluation data. A sparse class/stratum gets no upper bound and CLI exits nonzero; no unobserved adaptive history is covered.

## Additional hardening on this continuation

- **Effect provenance and delegated actors:** delayed local delivery now
  rebinds every committed release to its exact approval digest, destination,
  agent UID and lease, verifies the lease owner and distinct trusted review
  role, and refuses mutated records before writing real bytes. Negative
  controls mutate each authorization binding. Broker-shape tests reject
  cross-agent lease borrowing and client-supplied `agent_uid` impersonation.
  These simulated identities do not establish OS UID separation.
- **F6 operational usefulness:** a frozen manifest may additionally declare
  both `max_miss_upper` and `max_false_alarm_upper`. All simultaneous
  upper confidence bounds must meet both predeclared limits in every stratum
  for `conditional_limits_met`; a statistically computable but vacuous bound
  now fails that acceptance gate. This remains conditional statistical
  evidence, not adversarial per-history calibration or deployment assurance.
- **Immutable F6 receipts:** output creation uses `O_EXCL|O_NOFOLLOW` and
  fsync rather than a check-then-write path. Regression tests cover dangling
  and existing symlink targets to prevent redirection into frozen evidence.

## Verification and acceptance

```bash
python3 -m unittest discover -s trusted_stack -p 'test_*.py' -v
python3 -m unittest tools.test_monitor_calibration -v
lake exe cache get
lake env lean reviews/family-strengthening/Remaining.lean
lake env lean reviews/family-strengthening/EffectLifecycle.lean
python3 tools/joint_runtime_lean_difftest.py
python3 tools/build_registry.py --check
python3 tools/build_statement_catalog.py --check
python3 tools/build_status.py --check
python3 tools/check_scenarios.py
```

The newest-HEAD workflows `trusted-local-receiver`, `remaining-formal-families`, `monitor-calibration`, `trusted-effect-reference`, `consolidated-integrity`, `fast-checks`, `egress-boundary` and `scenario-a-repair` must be green before merge. Preserve exact kernel axiom output; exclude `sorryAx`. Changes to historical evidence, preregistrations or `ControlStack/EgressGate.lean` are forbidden.

## Irreducible outstanding trust and evidence gates

1. **Complete effect capture/OS refinement:** the local file receiver controls *one* broker-owned output directory. An untrusted process may still have other execution, networking, filesystem and delegated action routes. Only a separately controlled, experimentally validated capability-closed host/VM with verified effect coverage can discharge F1/F3/F8's global "every action" premise. Broker-owned file publication is not such a proof.
2. **Real monitor calibration:** finite iid held-out strata are not worst-case adaptive histories. Acquire sufficiently sized data under a signed, predeclared policy with stable thresholds and representative observation/response capture. Prove the conditional per-history hypothesis used by the F6 bounds; handle monitor correlations explicitly. No new empirical F6 success claim is warranted without that data.
3. **SC-01 original baseline:** the frozen TCG 0.25-second original useful-run receipt remains **0/64 baseline, 0/64 mediated**. A permitted suitable native hypervisor and separately versioned architecture/guest build or a native ARM64 KVM host are needed to run a valid newly preregistered usefulness test. Do not edit frozen receipts to make it pass.
4. **Independent trust anchor and reviewer:** obtain verified OS UID/secret separation, independent hardware/VM/effect custody, independent proof-statement fidelity review and recorded attestation of exact code/host/runtime hashes. No self-authored CI or model proof substitutes for an independent evaluation.

**Stop criterion:** all 28 scenario deployment-assurance claims stay CONDITIONAL until those real external premises are established.

---

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
