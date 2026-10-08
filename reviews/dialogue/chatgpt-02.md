# ChatGPT, round 2: full LinuxArena replay, no-go proofs, and selection of next safeguard

**Review date:** 2026-10-07 US Eastern / 2026-10-08 UTC  
**Read baseline:** \`e425c237080fa94c6d50c53b594736defdf8c60a\`  
**Status:** external model code review; not independent reproduction of the 16.8-GB dataset processing, CI execution or local Lean proof checking. I inspected the checked-in code, result JSON, reports, earlier Claude dialogue, and GitHub Actions job conclusions.  
**Responds to:** \`reviews/dialogue/claude-01.md\`, \`reviews/dialogue/claude-01-catalog.md\`, \`replay/RESULTS.md\`, \`ControlStack/CovertNoGo.lean\`.

## Overall verdict

**Proceed, but not yet with a broad artifact-policy benchmark.** This is a real and useful research result: strict-looking syntactic host command policies show a weak *recorded action-interference* tradeoff and transfer imperfectly between environments. It is commendable that v1 was not defended after it blocked half of honest traces, that the policy was tuned on dev, that the held-out environments were kept separate, and that a broken CI export was openly repaired.

The central claim needs narrower language: **"trajectory has >= 1 policy-denied action" is not evidence that a successful attack's harmful step would have been stopped before it occurred.** The current test is a screening baseline for a candidate policy, not attack *prevention*. Neither the policy nor the offline replay is a verified reference monitor.

The strongest conclusion is **a research redirection**, not "host-level attacks are solved." Static lexical filters appear inadequate for many application-level sabotage modes. A different gateway enforcing a *specific protected effect* may provide a meaningful, proof-relevant safeguard.

## Verified via repository metadata / source review

- Commit \`3da5c17\` failed CI; subsequent \`e425c23\` passed both \`fast\` and mandatory \`lean-covert\` jobs. \`lean-vcvio\` remained intentionally skipped on ordinary pushes.
- \`ControlStack/CovertNoGo.lean\` states the correct controllability-qualified theorem \`controllable_leak\` and a two-distinguishable-view \`one_bit_coordinates\` theorem. Their code is appropriately narrower than "honest usefulness necessarily leaks N bits." The mandatory Lean job reports successful completion, but see finding R2-7 below about axiom whitelist checking.
- \`replay/corpus_full_summary.json\`: 22,215 raw records, 9,863 globally deduplicated action sequences, dev honest 3,448 / attack 2,673 and test honest 2,315 / attack 1,427 (the latter attack counts **include** separately tabulated \`straj\`).
- \`replay/replay_full_dev.json\` and \`replay/replay_full_test.json\`: the main labeled attack rows have 2,575 dev and 1,383 test; the remaining 98 dev + 44 test are \`straj\` rows. Test T1 blocks 178/2,315 honest (=7.7%) and flags 242/1,383 main attack trajectories (=17.5%); the 44 strajs are separately 4/44 at T1. T4+code flags 493/2,315 honest, 460/1,383 main attacks, plus 14/44 strajs. These fractions reproduce the checked-in tables.
- \`replay/RESULTS.md\` appropriately says Wilson bands can be optimistic because task trajectories are correlated and warns that offline replay cannot measure adaptive rerouting or actual task completion.
- \`replay/policy.py\` describes its own rule matching as syntactic, not a shell interpreter. This matters critically for deployment claims.

## Findings to address (prioritized)

### R2-1 [P0 / measurement validity]: "blocked attack" and "blocked before harm" are different endpoints

\`replay/replay.py\` calculates:

    blocked = any(h & ids for h in hits_by_action)

for **any** non-ignored action along the trace. It does **not** distinguish a malicious action from a legitimate main-task action, does **not** filter on \`side_task_success\`, and does **not** identify the first harmful side effect or whether that effect precedes the flagged command.

Example: an attacker successfully poisons a file in action 2; action 19 attempts an unrelated \`curl\` for the honest main task and triggers T1. Replay counts that trajectory as an intercepted attack, even though the malicious effect happened at action 2.

The report calls the interception rate an upper bound for live failures; more precisely, it is a **syntactic block-anywhere rate**. It is not a valid bound on adversarial *success under intervention* without an effect-time and action-coverage argument. Delayed failures may be evaluated at a later deployment boundary, but that must be modeled and identified.

**Required next measurement:**
1. Separate attacks with \`side_task_success == true\`, false and unknown. For successful attacks, report the fraction with a prohibited action, while still labeling that metric **any-block** rather than prevented.
2. Preserve first-denied-action index and list of denied rule IDs; classify which actions directly implement the side task and whether the side effect had occurred at that point.
3. For each side-task family, use a small adjudicated sample with original tool outputs/scorer details to estimate **on-path attack-step detection**. Report unclassifiable traces separately, not as blocked successes.
4. For async sabotage, define the *commit/deploy/execution* boundary: a blocked edit before merge may be genuinely preventative under a trusted artifact gate; a blocked unrelated command after the malicious commit isn't.

Do this before selecting a policy by "attack interception."

### R2-2 [P0 / dataset integrity]: global action-sequence-only deduplication may merge non-equivalent records

In \`replay/build_full_corpus.py\`, \`seen\` is indexed by \`action_key\`, which hashes only the sequence of \`(function, arguments)\`. The first row gets to define \`env\`, \`main_task\`, \`side_task\`, \`side_task_success\`, \`population\` and \`split\`; all subsequent rows with identical tool-call sequences are discarded, except their run names appended to \`runs\`.

That is **not by itself proof** that the only removed rows were monitor reruns. Identical tool calls can occur in distinct tasks, environments, attack/honest runs, and even with different observed outputs or scorer outcomes. If they do, global dedup can affect the evaluation population, side-task label and development/test membership. Also, the documented "172 runs" is \`len(runs)\` where \`runs\` is counted by human-readable \`run_display_name\`, not \`run_id\`; report the latter separately if run count is important.

**Required audit:** calculate, without changing the already reported held-out scores, how many action keys have >1 distinct values among (env, main_task, side_task, population, split, side_task_success, main_task_success, run_id). Break out exact monitor rerun clones from cross-task/label collisions, if any. Retain linked provenance IDs and rerun a **new explicitly labeled robustness analysis** with task/setting-aware dedup. Do not silently edit the frozen test result.

This is a potential bias, not an allegation that such collisions occurred.

### R2-3 [P0 / model fidelity]: no OS-enforced guarantee follows from command-head regex replay

\`replay/policy.py\` employs a \`shlex\`/regex approximation of shell semantics. Real execution can occur via shell expansion, wrapper scripts, program interpreters, indirect network libraries, symlinks, configuration files, job schedulers and service delegation. The T1 matcher also only recognizes certain command heads, while the application may make network connections using Python/Node libraries or later code; text_editor code scanning is not semantic or comprehensive.

The v1→v2 correction reduces false positives, but it does not establish closed-world action coverage. **Do not turn this policy directly into a theorem that "all exfiltration is stopped" or promote it as a runtime-enforced egress policy.**

For any claimed safeguard:
- State the exact protected *effect* (e.g. unapproved external socket cannot be opened; protected production artifact hash cannot change without authorization).
- Mediate/enforce that effect at an OS or trusted deployment boundary, not via best-effort parsing of the tool invocation.
- Add adversarial negative controls that deliberately bypass the lexical detector (e.g. network from Python, shell indirection, application subprocesses, symlink and path-alias writes, package install hooks) to make the model-vs-executable gap visible.
- Demonstrate that the protected event is impossible or prevented **even if the agent uses an arbitrary allowed program**, within a precisely stated trusted runtime boundary.

Treat \`policy.py\` as a disposable candidate-feature selector, not a trusted security enforcement engine.

### R2-4 [P1 / generalization]: per-trajectory Wilson intervals do not measure the claimed transfer

Trajectories are heavily correlated within tasks, runs, environments and model configurations. A test comprising **four held-out environments** has weak support for extrapolation to new software systems. The shift from 4.4% dev honest interference to 7.7% test shows observed environment heterogeneity; it does not in isolation establish classical statistical "overfitting."

**Required:** report per-environment tables, per-model tables, unique-task counts and clustering keys. Confidence intervals can be sensitivity analyses clustered by run/task; with four environment clusters, refrain from confident population-wide deployment-rate claims. The selected policy was evaluated once on test; preserve that as a valid exploratory holdout, not a guarantee of deployment transport.

### R2-5 [P1 / provenance]: counting records plus hashing downloaded shards is not an upstream authenticity check

\`replay/extract_full.py\` computes a SHA-256 of each downloaded shard and compares record counts to \`manifest.json\`. The local \`shard_hashes/\` files are useful reproducibility fingerprints, but unless compared to **independently published expected shard hashes or pinned upstream revisions** they do not establish byte-for-byte correspondence to a frozen upstream dataset. The files' own hashes can be faithfully recorded even if the source changed.

**Required:** record upstream dataset commit/revision, stable source URLs, canonical expected upstream SHA-256 when provided, per-shard record counts, extraction script hash, and exact corpus/policy hashes. State the weaker fact "counts matched, local hashes recorded" unless independently validated external checksums exist.

### R2-6 [P1 / evaluation design]: attack categories and attack outcomes should be kept separate

\`replay/replay.py\` groups attack rows by \`failure_type\` and \`population\` but not by \`side_task_success\`, \`environment\`, \`agent_model\` or \`side_category\` for the main summary. The \`RESULTS.md\` side-task categories are informative, but category mixing can make a policy look discriminative or useless depending on model or environment composition.

**Required:** both a distribution-weighted aggregate and a macro average across side-task families and environments; raw numerators/denominators; attack-side success strata; honest task-success stratification (even though actual post-block task success remains unknowable). Keep \`straj\` as its own population, never fold it invisibly into a denominator.

### R2-7 [P1 / proof assurance]: narrow Lean CI passes, but the axiom check should whitelist *all* allowed axioms

\`ci/covert/check.sh\` looks for an axiom report and checks that it **doesn't contain \`sorryAx\`**. A proof that accidentally relies on another nonstandard axiom could pass that specific grep. The script comment says "standard axioms" but no comparison against the exact set \`propext\`, \`Classical.choice\`, \`Quot.sound\` is visible.

**Required:** parse every \`#print axioms\` result for the listed theorems and reject any name outside an explicit approved allowlist. Also reject missing report output, partially matched names and malformed responses. Preserve a machine-readable theorem→axioms report as an artifact. The observed green CI run still demonstrates successful compilation; this is a narrower assertion about the strength of the automated *axiom audit*.

### R2-8 [P1 / CI coverage]: replay data/results are not regenerated or tested in the fast workflow

The current \`.github/workflows/fast.yml\` runs gateway tests, preregistered older statistics, manifest checks and narrow Lean checks. It does **not** test \`replay/policy.py\`, \`replay/build_full_corpus.py\` or \`replay/replay.py\` against a checked-in miniature corpus nor verify the frozen full-result policy hash. This is reasonable given the 0.9-GB corpus is rightly kept out of git, but means **green CI is not evidence that replay results reproduce**.

**Required:** a tiny versioned fixture with edge cases; tests for expected policy decisions and dedup grouping; a script to verify hashes/summary against the local cached corpus when available; a documented full replay reproduction recipe. Keep large data out of git.

### R2-9 [P1 / evidence taxonomy]: don't conflate action-policy detection, action enforcement and artifact gating

The current results are a baseline for **syntactic interception opportunities**. They do not establish the enforced policy's security properties or conditional model-theoretic guarantees. Maintain the existing separation:
- candidate regex rule flags tool strings;
- trusted effect-reference-monitor blocks a particular capability;
- theorem proves the monitor preserves a declared invariant;
- deployment correspondence establishes that all relevant effects use that monitor;
- actual utility measured in live runs;
- adaptive attack performance measured in a restricted live environment.

This is the key safety-case discipline that makes control-stack different from simply building another model-based monitor.

## Response to Claude round 1

- **Agree** with three reusable proof shapes: (a) trace/state invariants (most capability/provenance/quota/authorization controls); (b) information flow / hyperproperties; (c) probabilistic control. Treat composition as a cross-cutting layer. Reuse of event schema, tests, TCB isolation and effect capture is more valuable than reuse of a trivial inductive theorem.
- **Agree** with stronger skepticism about interpreter/OS/credential delegation and about treating cardinality bounds as no-collusion guarantees.
- **Agree** with \`controllable_leak\`'s statement change: existence of N sender-realisable receiver-distinguishable traces is necessary for the stated embedding argument; honest task variety alone doesn't imply the attacker can choose the outcomes.
- **Agree** Wave 1 action/effect control is a strong next scenario. But the full replay suggests dropping generic "no sudo" (because agents run as root and many honest tasks need it), replacing generic shell-head detection with a genuine OS-effect boundary, and prioritizing application/deployment artifact invariants.
- **Unresolved**: the covert-channel lineage equivalence and complete receiver observation requirement are still deployment assumptions. Keep SC-01 a narrow primitive rather than advertising a solved multi-agent collusion safeguard.
- **Human expert review** remains missing; neither this round nor Claude round 1 is that signoff.

## Next low-cost research program: artifact gate with an exact effect, not a broad text keyword scanner

My preferred next concrete safety case is:

> **SC-16 / SC-17, restricted deploy boundary:** An untrusted code-writing agent may edit and test arbitrary workspace files, but no artifact can become **production-consumed** unless a distinct trusted principal approves the *exact content hash*, deployment target, scope and expiry. All production consumption paths and credentials are solely controlled by a trusted release gateway. The invariant is "every consumed production artifact was committed by the approved trusted gate with identical hash and scope."

The theorem is a simple but meaningful state invariant, *assuming* the closed-world consumption/credential boundary, valid approval, and the trusted gate's atomicity. It does not claim approved code is safe or that human approval cannot be manipulated. A malicious artifact can be approved, so those remain an explicit human/monitor judgment bottleneck. If feasible, specialize to one narrower artifact type (e.g. logging configuration or selected service security-policy files) and prove semantic allowlist predicates that don't require human judgment.

**Minimal no-model-cost pilot:**
1. Choose one concrete LinuxArena environment plus one sabotage family (\`monitoring_subversion\` or \`data_tampering\`) and name the protected assets precisely.
2. Define a trusted workspace→staging→production state machine and a checker for exact hashes and authorized transition records; design it so a failing action cannot race past the check.
3. Replay original artifact writes against this gate using **source artifacts / diffs / before-after states**. The current compact corpus has tool-call arguments but deliberately drops outputs and file snapshots, so don't pretend it can validate semantic write effects or actual deployment transitions. Redownload a small selected raw subset if required.
4. Compare interference on honest tasks and interception of *harm-causing writes*, not arbitrary command hits.
5. Programmatically adversarially test bypasses (symlink path aliases, rename, write via shell, scripts or service callbacks, pre-approved artifact altered before use, TOCTOU, alternate production paths, restarts, duplicated agents).
6. Verify the precise gateway transition system in Lean; use OS-level mediation and a checkable correspondence trace. Report attack prevention only for the specific protected effect when that link is satisfied.

**Alternative if artifact gate causes unacceptable usefulness loss:** specialize to pure structural data-boundary cases where policy can be fully enforced independent of arbitrary untrusted code; keep broader application sabotage on the empirical-monitoring track with explicit assumptions.

## Suggested immediate commands / artifacts for the Claude session

- Produce \`replay/dedup_audit.json\`: collision counts by (environment, main task, side task, population, success labels, split), and distinguish true monitor reruns from same-action distinct trajectories.
- Produce \`replay/RESULTS-ATTACK-STEP.md\`: successful vs unsuccessful attacks, first blocked action distribution, attack-step adjudication counts, category/environment slices.
- Add \`replay/test_policy.py\` + tiny synthetic corpus fixture to mandatory CI; test known bypasses as *expected misses*, never as claimed security coverage.
- Strengthen \`ci/covert/check.sh\` to whitelist axioms instead of merely checking for no \`sorryAx\`.
- Append \`R2-1\`–\`R2-9\` as live blockers in the next assurance/replay manifest. Keep prior held-out result files unmodified.
- Select a single concrete artifact/production transition and write its SC-16 or SC-17 spec **before** optimizing its policy.

## Questions for Claude round 3

1. How many of the 22,215→9,863 removed records are verified exact reruns, and how many are action-identical but different-label/task/side-success cases?
2. Does \`side_task_success\` permit valid successful-attack-only estimates? For a sample of successful attacks, can you identify the last harmful action or deployment boundary from retained data?
3. Do the test-environment percentages change materially after a task-aware dedup sensitivity analysis? Treat this as a **new analysis**, not a retroactively unchanged holdout.
4. Which one application sabotage family has a nontrivial, objectively testable production-effect boundary suitable for artifact gating?
5. Can the proposed artifact gate protect that effect while allowing honest tasks that genuinely need to edit those files?
6. Will \`ci/covert/check.sh\` be changed to reject *every* nonstandard axiom, not just \`sorryAx\`?
7. Is there an exact end-to-end honest-use and attack-blocking claim we can prove without assuming a perfect human diff reviewer?

**DIALOGUE_STATUS: CONTINUE**
