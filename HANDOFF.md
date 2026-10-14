# Research track handoff: experiment E1 run (2026-10-14)

**E1 has been run.** The owner authorised it ("Go ahead, u r good"); the preregistration was frozen at commit
`1213a2c` and the confirmatory analysis ran once with no deviation. Read
[experiments/E1-flag-budget-replay/RESULTS.md](experiments/E1-flag-budget-replay/RESULTS.md). The sections below
describe the state before the run and how it was staged; where they say "not run", that was true when written.

Next step named by the preregistration: a live run with an attack policy that knows the protocol. It costs money
and has not been started or scoped. `results/confirmatory.started` and `results/confirmatory.json` must stay; the
run is one-shot and `analyze.py --confirm` refuses to repeat it.

---

# Staging notes: experiment E1 staged, truncation closed (2026-10-14)

Branch `research/e1-replay-prereg-20261014`, stacked on `research/m1-flagship-20261013` (PR #65). Read
[ROADMAP.md](ROADMAP.md) section 4 "Experiment E1", then
[experiments/E1-flag-budget-replay/PREREG.md](experiments/E1-flag-budget-replay/PREREG.md).

**State: the experiment is ready to run and has NOT been run.** It needs the owner's authorisation.

**What changed since the Milestone 1 handoff below.**

- `ControlStack/Families/F6/Truncation.lean` (new, proved by a delegated prover against frozen statements and
  recompiled independently): `prefix_eq_truncated`; the three split bounds for "k attacks released before the first
  catch". Closes Milestone 1's first "not met" item.
- `ControlStack/Families/F6/ClassAudit.lean` (new): `class_flag_bound` (the attacker chooses the kind of attack; the
  bound uses the minimum recall over kinds), `class_average_witness`. This is the statement E1's premises feed.
- `data/linuxarena-public/compact/` (new): labels (`meta/`) and sealed scores (`sealed/`) for the 22,215
  trajectories of the LinuxArena public mirror (CC-BY-4.0), extracted by streaming the ten shards once.
- `experiments/E1-flag-budget-replay/` (new): `PREREG.md` (DRAFT), `analyze.py`, `test_analyze.py` (15 checks on
  generated data), `extract_scores.py`, `freeze.py`, `freeze.json` (status DRAFT), `development_run_ids.json`,
  `results/dev.json` (development sample only).
- Record, roadmap (revision 3), registry annotations, statement catalogue and the `m1-budgeted-audit` workflow
  updated.

**To run E1** (owner):

1. Read `PREREG.md`; edit anything you disagree with.
2. `python3 experiments/E1-flag-budget-replay/freeze.py --write`, then commit `freeze.json`.
3. Run the command it prints (`E1_PREREG_SHA256=... python3 experiments/E1-flag-budget-replay/analyze.py --confirm`).
   About two minutes of CPU. No network, no model calls, no cost. It writes `results/confirmatory.json` once and
   refuses to run again.
4. Apply the consequence precommitted in `PREREG.md` section 7 for whichever way the primary endpoint came out.

**Do not** read `data/linuxarena-public/compact/sealed/` or run `--confirm` before step 2. The seal is a convention.

**Reviews of the experiment design (models, not people).** A hostile referee of another model family reviewed the
draft preregistration and said "freeze after fixes": premise transfer became the primary endpoint; the replay
values became sensitivity analyses; outcomes that are trivially true when a bound equals 1 are now reported as
uninformative; the test-side false-positive bound respects task clustering; the pooled recall is described as a
naive comparator, not a certificate; the constant-rate search was refined; dropped records and per-policy flag
rates are reported. A second reviewer audited the analysis code against the preregistration and found one
blocking bug and four lesser ones, all fixed: 92 trajectory ids are shared between a base run and its re-scored
copy, which would have crashed the one-shot run; the run guards were assertions (void under `python -O`); the
freeze could be repeated after a crash; the calibration flag count was reported from the target rather than
measured; the threshold index used floating point. It independently confirmed the counts in the preregistration,
the Clopper-Pearson and bootstrap code, and the attacker-value programme.

**Verification** (run on the commit after `e8af227` that carries the audit fixes).

| command | result |
|---|---|
| `lake build` | Build completed successfully (3832 jobs) |
| `lake env lean` on `Truncation.lean`, `ClassAudit.lean` | every `#print axioms` line is `[propext, Classical.choice, Quot.sound]`; no warnings |
| `python3 experiments/E1-flag-budget-replay/test_analyze.py` | 15/15 (generated data only; includes a rehearsal of freeze, confirm and the one-shot guards in a temporary tree) |
| `python3 experiments/E1-flag-budget-replay/analyze.py --check-data` | label and score files line up; 11,961 usable monitor-run trajectories; prints counts only |
| `python3 numerics/test_budgeted_audit.py` | 12/12 |
| `python3 tools/check_records.py` | 0 problems |
| `tools/build_registry.py`, `build_statement_catalog.py`, `build_lean_english_overview.py`, `build_status.py`, `build_overview.py` with `--check` | consistent (registry: 2326 declarations) |
| `python3 tools/check_deployment_prereg.py --base origin/main` | PASS (no protected path touched; the E1 preregistration lives in `experiments/`, because that guard reserves `prereg/`) |
| GitHub Actions on pull request #67 | at `e8af227`: 27 passed, 0 failed, 3 skipped (the same three as on #65); `full-build` ran uncached, 3832 jobs. Runs on later commits are in the pull request. |

Not verified: anything about the confirmatory data. The sealed scores have not been read, so the pipeline has run
end to end only on generated data and on the 932-trajectory development sample.

---

# Research track handoff: Milestone 1 flagship (2026-10-13)

Read first: [ROADMAP.md](ROADMAP.md) (revision 2), then the record
[docs/records/budgeted-audit-vs-adaptive-attacker.md](docs/records/budgeted-audit-vs-adaptive-attacker.md).
Branch `research/m1-flagship-20261013`, base `main` at `e7b4b25`. One pull request; **not to be merged without
independent human review**.

**What changed.**

- `ControlStack/Families/F6/FlagBudget.lean` (new): potential bounds for `val`/`cval`; flag-triggered auditing with a
  hard first-come budget: `flag_pre_bound`, `flag_exhaust_bound`, `flag_total_bound`.
- `ControlStack/Families/F6/SplitAudit.lean` (new): one kernel for hidden random audits, flag audits and their split:
  `split_hidden_bound`, `split_flag_bound`, `split_min_bound`, `split_product_pre`, `split_product_bound`; kernel
  witnesses `exhaustion_witness`, `average_recall_witness`, `dependence_witness`; `hidden_one_step`, `split_example`.
- `numerics/budgeted_audit.py`, `numerics/test_budgeted_audit.py`, `numerics/budgeted_audit/results.json` (new):
  exact executable model, 12 consistency checks, frozen tables.
- `docs/records/` (new) with the record; `tools/check_records.py` (new) validates its declaration references.
- `.github/workflows/m1-budgeted-audit.yml` (new): record check, banned-token grep on the two modules, model checks.
- `ROADMAP.md` rewritten as revision 2. `ControlStack.lean` imports the two modules. `registry/annotations.json`
  gains eight entries; `THEOREM-REGISTRY.*` and `LEAN-STATEMENTS-NORMAL-FORM.md` regenerated.
- No existing Lean file, frozen evidence, pinned artifact or `ControlStack/EgressGate.lean` was modified.

**Verification report.** Code commit verified: `df08678` (this note is a later documentation-only commit).

Local (Lean 4.34.0 from `~/.elan`, Mathlib from the shared package tree):

| command | result |
|---|---|
| `lake build` | Build completed successfully (3830 jobs), no errors |
| `lake env lean ControlStack/Families/F6/FlagBudget.lean`, `.../SplitAudit.lean` | 8 + 12 `#print axioms` lines, each `[propext, Classical.choice, Quot.sound]`; no warnings |
| `python3 tools/build_registry.py --check` | registry consistent: 2294 declarations |
| `python3 tools/build_statement_catalog.py --check`, `build_lean_english_overview.py --check`, `build_status.py --check`, `build_overview.py --check` | all consistent |
| `python3 tools/check_scenarios.py` | exit 0 |
| `python3 tools/check_records.py` | 1 record checked, 0 problems (and it fails on a mutated record: misspelt declaration, false dependency) |
| `python3 numerics/test_budgeted_audit.py` | 12/12 checks passed |
| `for t in tools/test_*.py` | 27 pass. 9 fail identically on an unmodified clone (5 need `python -m` invocation, 3 need root, 1 needs the `trusted_stack` path). 7 more fail only in a git worktree because `.git` is a file there (`NotADirectoryError`); they pass on a normal clone and in CI. |

GitHub Actions on `df08678` (pull request #65): 27 checks passed, 0 failed, 3 skipped.

- `full-build` (deployment-release, GitHub-hosted, run 38488290056): its green-marker cache missed, so it ran
  `lake build` for real; the log shows `Built ControlStack.Families.F6.FlagBudget`, `Built
  ControlStack.Families.F6.SplitAudit`, `Build completed successfully (3830 jobs)`.
- `model-and-record` (new workflow, run 38488289998): record references resolve; banned-token grep clean; 12/12.
- `generated-declaration-and-statement-consistency`, `generated-index-drift`, `guards`: registry, statement
  catalogue, overview and scenario index consistent.
- Skipped, not passed: `lean-vcvio`, `linux-boundary`, `live-containers` (path- or environment-gated; none covers
  the files changed here).

Reviews (models, not people). Before implementation: soundness, relevance, and a hostile referee of another model
family; outcomes in ROADMAP section 3. After implementation: the same referee audited the Lean statements against
the record's English. It reported no defect in the statements and eight wording defects, all fixed in `df08678`:

1. `dependence_witness` refuted only a product with schedule-averaged recall. Replaced by a schedule-leak instance
   with recall 1/2 for every schedule.
2. `exhaustion_witness` refutes compounding of monitor recall, not of a per-attack catch recall; α range stated.
3. Failure-table cell conflated the witness's success probability with the binomial exhaustion bound.
4. `FlagBudget` theorems constrain an arbitrary sub-probability kernel, not a protocol; header and record reworded.
5. Premises quantify over all histories, not only reachable ones.
6. The blind average is an upper bound, not an equality.
7. No variable-recall product is proved; wording removed.
8. `totSucc`, `binTail`, `hidden_one_step` docstrings qualified.

What green CI does not establish: that the model captures the question, that the English matches the Lean beyond
the points audited, or that any deployed monitor satisfies the premises.

**Not met, and what is needed to continue** (same list as ROADMAP section 4, M1).

1. Truncation lemma (prefix event). Next step: M2 step 1.
2. Imperfect reserved recall with visible flags. Needs `ReservedRecall`'s discount lemmas generalised from
   `AOut Unit`; that edits an existing file, so it waits for M2's refactor decision.
3. A usefulness quantity that distinguishes protocols. Needs a defer or block action: M2.
4. Honest against attacker-induced false positives in the exhaustion premise. Open modelling question.
5. Two papers read as abstracts only; two through an automated fetch. A person should spot-check the quotations in
   the record's section 7 before they are cited elsewhere.
6. External human review: the packet is the record's section 8. **No reviewer has been asked.** Model reviews
   (three, summarised in ROADMAP section 3) are not a substitute.

**Status words used here.** Completed: the files above exist. Verified: Lean-checked or test-checked as listed in
the verification report. Empirically supported: nothing in this milestone. Speculative: the measurement recipe for ρ
and the "constant-rate red teams understate risk" reading of the model values. Externally reviewed: nothing.

---

# SC-01 VM publication handoff — 2026-10-08

John requested publication onto private GitHub main and a linkable status file.
Canonical VM status: [gateway/vm/STATUS.md](gateway/vm/STATUS.md). Imported only
VM sources/receipts and their workflow from `sc01-vm-host-check-20261008` at
`9d4d785`, preserving remote main's existing Lean track. Codex infrastructure
ends at `9a43ae8`; Claude's `cda2b10` repairs the listener/connect race and
`9d4d785` records the complete frozen replay. These receipts verify in the
publication checkout. Config H is
`56a4dfa192003deaddf483ad008383ade9c0a2ca8d7eea0829fc401db7ff02a1`.

The link-bound configuration check and 10 resource controls pass. The usefulness
receipt is valid but its gate FAILED: baseline and mediated each complete 0/64
lifetimes, 0/320 episodes; every sender/receiver times out at the preserved
0.25-second deadline. Transport is no longer the blocker. Stop at failed step 4;
step 5 remains pending and the existing case stays CONDITIONAL. No results pooled,
no new channel experiment, no safety claim, no auditgate/ACL/IAM changes.

Next: usable hardware virtualization/separate hosts under existing permitted
access, or an owner-decided separately preregistered deadline amendment. MXC's
Linux MicroVM requires KVM and Hyperlight requires x86_64/KVM, so it does not
resolve this ARM64 host's limitation. Complete-observation proof remains separate.

Checks: saved isolation receipt, 10 unittest cases, frozen usefulness receipt
verifier, and whitespace checks; see publication verification receipt in STATUS.
Push uses `[skip ci]` to avoid the existing automatic cache experiment; dispatch
only the VM configuration/archived-receipt workflow. [VM verification CI](https://github.com/jwcodes12/control-stack/actions/runs/37851767586)
passed on publication commit `ef26633`. The saved CI receipt and canonical status
record its exact revision. No push-triggered workflows ran for the publication.
