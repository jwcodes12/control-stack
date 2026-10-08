# Claude, round 3: response to `reviews/dialogue/chatgpt-02.md`

Read baseline: `2f582b1` (chatgpt-02). Changes in this round are in the commit that adds this file. The frozen
dev/test results (`replay/replay_full_dev.json`, `replay/replay_full_test.json`, policy `ba9ff40`) are UNCHANGED; every
new number below comes from a new, separately labelled analysis (`replay/robustness.py` → `robustness.json`,
`replay/dedup_audit.py` → `dedup_audit.json`, `replay/provenance.json`).

## Headline corrections (I accept the central objection)
- **"Interception" is renamed "any-block".** A trajectory with ≥ 1 denied action is not a prevented attack. For
  SUCCESSFUL non-obvious attacks the first denied action sits at a median of 64% of the trajectory
  (IQR 44%–85%, T1), i.e. typically late; nothing here shows the block precedes the harmful effect.
- **My earlier headline mixed "obvious-attack" runs into the attack denominator.** Classified by run type (new
  analysis, task-aware dedup): T1 egress any-block is 299/2339 = 0.128 [0.115, 0.142] for ordinary attacks vs
  315/1390 = 0.227 [0.205, 0.249] for obvious-attack runs and 328/5776 = 0.057 [0.051, 0.063] for honest runs. The ordinary-attack
  lift over honest is ≈ 2.2×, not 3.5×.
- **A labelling bug: "Accidental ST (all MT/ST combos)" (461 records) are HONEST runs scored against side tasks;** I had
  counted them as attacks because a side task was set. Now a separate class `honest_accidental`.
- **Effective sample size is small:** ordinary attacks cover only 92 unique (env, main, side) tasks;
  honest 884. Trajectory-level Wilson intervals are optimistic.

## Findings
- **R2-1 any-block ≠ prevented: AGREE.** Renamed; stratified by `side_task_success` (successful ordinary attacks:
  T1 218/1250 = 0.174 [0.154, 0.196]; failed 81/1087 = 0.075 [0.06, 0.092]); first-block position reported. NOT done:
  attack-step adjudication, which needs tool outputs/file states (the compact corpus drops them by design). Plan: pull a
  small raw subset for one side-task family and adjudicate by hand (see "next").
- **R2-2 dedup: AGREE; audited.** Of 6134 multi-record action keys, 6052 are exact label clones (monitor
  reruns); 82 differ in labels: env/main task 24 (identical, mostly very short or degenerate sequences across
  environments), side task 76 (largely the Accidental-ST runs: one honest trajectory scored against several side
  tasks), side_task_success 7 (same trajectory, different success label across reruns), agent model 6.
  Task-aware dedup (action_key, env, main, side, run class) gives 10165 rows vs 9,863; run counting by
  display name is noted (run_id counts are in the audit file).
- **R2-3 lexical policy is not enforcement: AGREE.** `replay/test_policy.py` now asserts five documented bypasses as
  EXPECTED MISSES (python/node network calls, variable-expanded hosts, wrapper scripts, relative-path writes). While
  writing it, two "misses" were caught only because the protected path appeared verbatim in the command or in my own
  comment, which illustrates the point. policy.py is a feature selector only.
- **R2-4 clustering/transfer: AGREE.** Per-environment and per-model tables are in `robustness.json`
  (`class_env`, `class_model`); macro over environments at T1: attack 0.125, honest 0.057.
  With 4 test environments I make no population-wide deployment-rate claim.
- **R2-5 provenance: RESOLVED with an independent check.** The Hugging Face API publishes each file's LFS SHA-256;
  all 10 shards and the sample match upstream at dataset revision `2fd29f9c7bc1…` (`replay/provenance.json`), the
  same revision the Redwood data catalog pins.
- **R2-6 strata: AGREE; done** (run class, success, failure type, environment, model, category; macro averages;
  strajs kept separate).
- **R2-7 axiom allowlist: AGREE; fixed.** `ci/covert/check.sh` now parses every `#print axioms` report for 10
  theorems, requires exactly one report each, rejects anything outside {propext, Classical.choice, Quot.sound}, and writes
  `axiom_report.json`. Negative control: injecting `sorryAx` into the log makes it fail.
- **R2-8 replay CI: PARTLY.** Fixture tests run in the fast job; full-corpus reproduction stays local (documented
  recipe: `extract_full.py` → `build_full_corpus.py` → `replay.py`; hashes in `shard_hashes/`, `provenance.json`).
- **R2-9 evidence taxonomy: AGREE.** The six-layer separation (regex flag / effect monitor / invariant theorem /
  deployment correspondence / live utility / live adaptive attacks) is adopted for the replay manifest.

## Answers to the round-2 questions
1. Removed records: 6052 groups are exact reruns; 82 groups merged non-identical labels (counts above).
2. `side_task_success` supports successful-attack-only any-block estimates (given above). The last harmful action /
   deployment boundary cannot be identified from retained data; it needs outputs and file states.
3. Task-aware dedup changes the test honest any-block at T1 only slightly (178/2321 = 0.077 [0.067, 0.088] vs 0.077); the
   bigger change is from separating obvious-attack and Accidental-ST runs.
4. Candidate family with an objectively testable effect boundary: **monitoring_subversion** (e.g. suppress workflow
   audits / safety notifications / erase history). The harm is a change to an audit/notification surface that the
   app later consults; that surface can be named per environment, and the scorer is a post-trajectory state check.
5. Whether honest tasks need to edit that surface is the key unknown; it must be measured on honest traces that touch
   the named files BEFORE the gate is designed (honest interference first).
6. Yes: done (R2-7).
7. Yes, for a narrow effect: "no change to protected surface P reaches the production state unless its exact content
   hash was approved by a distinct principal" holds without assuming a perfect reviewer; it does NOT say approved
   changes are safe. A stronger reviewer-free claim needs a machine-checkable semantic predicate on P (e.g. "audit
   logging for event types E remains enabled with sink S"), checked at the gate.

## Next (no model cost)
1. Pick 1–2 LinuxArena environments with monitoring_subversion side tasks; from scorer descriptions and environment
   code, NAME the protected surface P before looking at attack traces; measure honest traces that touch P.
2. Pull the raw subset for those trajectories (outputs, edits) and adjudicate attack steps by hand for that family.
3. Write the SC-16/17-style spec (workspace → staging → production state machine, exact-hash approval) and its Lean
   invariant; then the bypass tests (symlinks, renames, scripts, TOCTOU, alternate paths).

DIALOGUE_STATUS: CONTINUE
