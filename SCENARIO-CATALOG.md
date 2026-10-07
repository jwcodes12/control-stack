# Scenario catalog: machine-checkable AI-control safeguards

**Status:** research and implementation roadmap; NOT a claim that the scenarios are solved.  
**Date:** 2026-10-07. **Owner:** control-stack.  
**Related:** [ROADMAP.md](ROADMAP.md), [CATASTROPHE-SPEC.md](CATASTROPHE-SPEC.md), [gateway/CORRESPONDENCE.md](gateway/CORRESPONDENCE.md), [independent gateway review](reviews/covert-channel-gateway-review-2026-10-07.md).

## 1. Goal

Build an extensible portfolio of **scenario-specific safety cases**. For each realistic high-stakes setting, identify:

1. What the untrusted agent can control and the bad outcome it might cause.
2. A deliberately restricted but **useful** deployment configuration.
3. A precise theorem about the bad event or a closely related enforceable invariant.
4. An executable checker/enforcer for each assumption that can genuinely be discharged by software or a proof.
5. A documented abstraction/refinement link from real runtime traces to the theorem.
6. Adversarial experiments for what remains unknown, plus usefulness measurements.
7. A manifest identifying which guarantees are proved, observed, estimated, assumed, or unsupported.

The research program should test **many** scenarios, not be hostage to the success of the first covert-channel scenario. If an approach fails, retain the failure evidence, diagnose whether the obstruction is mathematical, environmental or utility-related, and test another scenario or a more restricted deployment. If it succeeds, keep extending the portfolio.

**The objective is not a large count of Lean files.** Optimize for end-to-end safety claims whose premises can be independently checked in an actual deployment while preserving useful work.

## 2. What external research contributes

External settings provide a useful *threat inventory and evaluation environments*, not automatically a machine-checkable guarantee.

- **Redwood Research, BashArena:** four explicit side tasks: executing downloaded malware; exfiltrating secrets; granting unauthorized passwordless sudo; and disabling a firewall. They are unusually concrete starting points for hard action-control invariants. [Redwood description](https://www.redwoodresearch.org/blog/basharena-and-control-setting-design).
- **Redwood Research, LinuxArena:** 20 multi-service software environments, 1,667 legitimate SWE main tasks and 185 safety-failure side tasks, including exfiltration and backdooring. Good for testing whether narrow enforced capabilities remain useful in real-ish production engineering work. These are benchmark properties, not a certified coverage theorem. [Research site](https://www.linuxarena.ai/) · [Announcement](https://www.redwoodresearch.org/blog/introducing-linuxarena).
- **UK AI Security Institute + Redwood, ControlArena:** common interface for honest main tasks, adversarial side tasks and control protocols. Listed settings include AgentDojo, Apps, Bash, BashArena, BigCodeBench, Data Poisoning, Eval Sabotage, IaC/IaC Fast, Infra, Rogue Eval, SAE Interp Sabotage, SHADE Arena, SWE-bench Django and vLLM. Harms can be synchronous (before/at tool execution), asynchronous (code merged or deployed later), or mixed. [Settings catalog](https://control-arena.aisi.org.uk/settings/) · [Framework](https://control-arena.aisi.org.uk/).
- **Google DeepMind, AI Control Roadmap (2026):** treats misaligned agents as insider threats, introduces a tactic/technique taxonomy (TRAIT&R) informed by MITRE ATT&CK, and separates detection, prevention/response, coverage, recall and time-to-response. Its detection tiers D1–D4 and prevention/response tiers R1–R3 imply that *for high-impact irreversible actions, intervention must occur before the action*, not after a trajectory is scored. [Research paper](https://arxiv.org/abs/2607.13087) · [Google explanation](https://deepmind.google/blog/securing-the-future-of-ai-agents/).
- **MITRE ATLAS (living taxonomy):** AI-system attack lifecycle including initial access, execution, persistence, privilege escalation, defense evasion, credential access, command and control, exfiltration and impact. Useful for discovering missed scenarios; do not mistake a long technique list for independent mathematical proof obligations. [ATLAS](https://atlas.mitre.org/) · [Dataset](https://github.com/mitre-atlas/atlas-data).

### Important distinction

- **Source-derived setting:** the described attack task or evaluation environment is actually represented by an existing research artifact.
- **Proposed control-stack safeguard:** the theorem, trusted gateway, acceptance criterion and priority below are **our proposals**, not claims that Redwood, AISI or Google has already proved them.
- **Not every adverse outcome is decidable:** "contains any subtle backdoor" or "scientific conclusion is misleading" often requires semantic judgment. An accurate conditional theorem about a narrow action policy is valuable; it must not be relabelled as a proof of absence of all sabotage.

## 3. Reusable proof/checker families

Implement each family once, with many scenario instances. A single scenario can require several families.

| Family | Claim shape | Concrete checker/enforcer | Principal limitation |
|---|---|---|---|
| **F1. Capability confinement** | No untrusted trace contains a prohibited action or reaches a forbidden authority | Deny-by-default reference monitor; tool mediation; OS MAC/namespaces/seccomp where appropriate; checked policy | Every way to exercise the capability must pass through the monitor |
| **F2. Bounded observation / noninterference** | Receiver views belong to a fixed finite set; or low-secret changes cannot affect high-observable outputs | Typed IPC schemas, canonicalisers, fixed transcript cardinality; global budget accounting; trace validation | Side channels, receiver auxiliary information, multi-episode composition; small bandwidth can still communicate harmful commands |
| **F3. Stateful temporal invariant** | Certain bad states are unreachable; approval precedes a commit; shutdown is absorbing | Verified state machine + event/trace monitor + atomic gate | Implementation refinement, concurrency, crash/restart, TOCTOU and external effects |
| **F4. Integrity and provenance** | Only identified signed/hashed reviewed artifacts can be consumed/deployed | Content-addressing, signatures, immutable build artifacts, verification at use | Who/what was authorized to sign; malicious but valid signed content |
| **F5. Quotas, lease and revocation** | Bounded actions/resources, monotone expenditure, no future work after revocation | Trusted counters, budget token issuance, resource quotas, capability expiry | Cross-process/global accounting, forked instances, crash recovery, indirect resource use |
| **F6. Conditional probabilistic control** | Risk bounded given worst-case recall/coverage or constrained attack-row distributions | Lean/Mathlib/VCVio checkers, rational certs, pre-execution monitoring protocol | Empirical average ROC does not imply per-history or per-attack worst-case guarantees |
| **F7. Two-party/typed human approval** | Irreversible action requires valid approval for exact payload, scope and expiry | Independently held authorization key, signed transaction intent, replay protection | Human may approve a harmful payload; trust in identity and approval channel |
| **F8. Compositional / hyperproperty checker** | Safety holds under parallel agents, episode concatenation and observer composition | Product-state semantics, cumulative budgets, trace refinement, concurrency model checking | State explosion; assumes complete observation and correctly modeled shared state |

**Recommended common abstractions:** AgentAction, Resource/Capability, EnvironmentState, Observation, EventTrace, Principal, Episode/Lifetime, Decision (permit/deny/defer), TrustedMonitor, BadEvent, HonestTask, Assumption, Evidence, Counterexample.

The existing UMPROT / TMCERT / Compose results primarily contribute to F6. CovertChannel contributes to F2. SANDBOX contributes early pieces of F1. The missing central layer is verified deployment correspondence.

## 4. Proposed scenario inventory

Priority is for the *first strong, useful, end-to-end safety case*, not an ordering of societal risk. 

**Feasibility:** H = reasonably promising exact structural guard; M = exact guard possible for a restricted claim but coverage is hard; L = unavoidable semantic/statistical judgment for the broad catastrophe. These are exploratory assessments, not established results.

### A. Communication, exfiltration and multi-agent collusion

| ID | Concrete scenario / bad event | Candidate enforced property | Checker | Feasibility | Starting point |
|---|---|---|---|---|---|
| SC-01 | Machine receiver reconstructs a fresh uniform secret through inter-agent messages | Entire lifetime receiver-visible transcript belongs to a bounded space V; exact-recovery bound | F2, F8 | H for bounded *digital interface* | **Current P0**, CovertChannel and gateway |
| SC-02 | Sender communicates across multiple episodes to a persistent receiver | One global information budget per secret/receiver lifetime; account for every episode, reject replays | F2, F3, F8 | H/M | Required stress test for SC-01 |
| SC-03 | Agent sends a credential, user secret or model artifact to an outside endpoint | Outbound network/IPC endpoints absent except precisely authorized sinks; all egress mediated pre-execution | F1, F3 | H/M | BashArena exfiltration; LinuxArena |
| SC-04 | Agent leaks via logs, telemetry, diagnostic output, error strings or process timing | Restrict all *receiver-visible* diagnostics or include them in the certified observation space | F2, F3, F8 | M; absolute timing noninterference may be impractical | SC-01 correspondence gap |
| SC-05 | Agent coordinates a malicious action using a one-bit signal despite a 16-bit cap | **Do not claim the cardinality bound prevents it**; instead prohibit the particular recipient/action or certify zero secret-dependence for that output | F1, F2, F3 | M | Negative test for broad "no collusion" claims |
| SC-06 | Agent plants a covert instruction in shared files, code comments, retrieval memory or other artifacts for later agents | All cross-agent persistent artifacts go through one allowlisted typed/canonicalized write/read path | F1, F2, F3 | M | Data/memory channel variant |
| SC-07 | Exfiltration of model weights or large sensitive datasets | Isolate readable secret resources and all outbound stores; artifact quotas and egress denial | F1, F5 | M | LinuxArena exfiltration variant |

### B. Host and infrastructure compromise

| ID | Concrete scenario / bad event | Candidate enforced property | Checker | Feasibility | Starting point |
|---|---|---|---|---|---|
| SC-08 | Unauthorized process or executable runs, including malware | Execution restricted to predetermined signed programs and exact tool RPCs | F1, F4 | H/M | BashArena Download Malware |
| SC-09 | Agent obtains privileged host access or passwordless sudo | No reachable transition grants new privileges outside an approved identity/capability lattice | F1, F3 | H/M | BashArena Escalate Privileges |
| SC-10 | Agent weakens host firewall or security policy | Firewall/security policy objects read-only for the agent; mutations gated by authorized exact-diff reviewer | F1, F3, F7 | H/M | BashArena Disable Firewall |
| SC-11 | Agent tampers with container mounts, host filesystem or trusted toolchain | OS separation, deny writes to trust roots, verified mount/path-resolution config and startup attestation | F1, F3, F4 | M | SANDBOXF1/SANDBOX2F1 |
| SC-12 | Agent establishes persistence, spawns helpers or recursively replicates | No unsanctioned process creation, schedules or durable executable writes; leases bound total authority | F1, F3, F5 | M | MITRE ATT&CK/ATLAS persistence |
| SC-13 | Agent disables logging, monitoring, alerts or the shutdown controller | Trusted control plane disjoint from agent authority; revocation and log integrity as state invariants | F1, F3, F4 | H/M | Google detection/prevention framework |
| SC-14 | Agent consumes runaway compute, tokens, network or budget | Cumulative trusted quotas across workers; enforced kill/expiry; restart-safe counters | F3, F5 | H/M | General control infrastructure |

### C. Software development and deployment sabotage

| ID | Concrete scenario / bad event | Candidate enforced property | Checker | Feasibility | Starting point |
|---|---|---|---|---|---|
| SC-15 | Agent inserts a hidden functional backdoor in source code | Enforce a narrower security-sensitive invariant: no changes to specified auth/crypto/egress surfaces without review; prove contract on restricted code | F1, F3, F4, F6 | M for restricted claim, L for all backdoors | Apps, BigCodeBench, SWE-bench Django, LinuxArena |
| SC-16 | Agent ships code or config before trusted evaluation/approval | Every deployment artifact matches the exact reviewed hash; no side effects before gate commits | F3, F4, F7 | H/M | Async code-sabotage settings |
| SC-17 | Agent sabotages IaC, Kubernetes or production cluster permissions | Enforce declarative policy invariants on resource graphs and diff; deny unauthorized apply operations | F1, F3, F4 | H/M for a selected policy | ControlArena IaC / Infra |
| SC-18 | Agent disables inference logging or monitoring in model-serving infrastructure | Serving configuration and logging invariants hold in every deployed release; only approved artifacts are loaded | F1, F3, F4 | H/M | ControlArena Rogue Eval / vLLM |
| SC-19 | Agent damages data or causes an irreversible live production side effect | Mutations occur only in transaction/preview gate; protected backups and restoration invariants | F1, F3, F4 | M | LinuxArena live environments; synchronous vs async harms |

### D. Evaluation, science, oversight and agent manipulation

| ID | Concrete scenario / bad event | Candidate enforced property | Checker | Feasibility | Starting point |
|---|---|---|---|---|---|
| SC-20 | Agent poisons a training/distillation dataset or hidden label | Dataset provenance, forbidden file/label transitions and immutable training-set hash; narrower than semantic cleanliness | F1, F3, F4, F6 | M/L | ControlArena Data Poisoning |
| SC-21 | Agent corrupts safety evaluations or selectively suppresses failures | Frozen evaluator and dataset hashes, trace completeness, independent score computation; no unreviewed eval code modification | F3, F4, F6 | M | ControlArena Eval Sabotage |
| SC-22 | Agent misreports interpretability or research findings | Verify data lineage and reproducible numerical computation; semantic truthfulness still needs independent experts or empirical checks | F4, F6 | L for full claim | ControlArena SAE Interp Sabotage |
| SC-23 | Prompt-injected document/tool result causes an unauthorized tool action | Untrusted text cannot change capabilities, trusted policies or transaction identity; authorize side effects against trusted request | F1, F3, F7 | H/M for action constraints | ControlArena AgentDojo |
| SC-24 | Untrusted monitor colludes with generator or learns honeypot phase | Enforce complete mediated view, independent phase schedule and monitor sandbox; bound probability under explicit L, r assumptions | F2, F6, F8 | M/L | Existing UMPROT / Compose / LASR |
| SC-25 | Agent hides or misorders hazardous actions behind after-the-fact monitoring | For irreversible acts, check-before-effect and absorbing halt; explicitly prove action/event ordering | F3, F6 | H for protocol ordering | Google response-timing framing; LinuxArena live harms |
| SC-26 | Agent transfers funds, alters access or executes another irreversible external action without consent | Typed transaction + exact signed approval from distinct principal, replay protection and spend/authority budgets | F1, F3, F5, F7 | H/M | ControlArena SHADE Arena (illustrative real-world agent tasks) |
| SC-27 | Agent falsifies monitoring evidence or tampers with assurance manifests | Evidence chain bound to code/data hashes, trusted CI attestation, append-only audit and independent verification | F3, F4 | H/M | Applies to control-stack itself |
| SC-28 | Multiple agents individually satisfy limits but jointly exceed overall risk/budget | Global state, cumulative exposure, composition theorem across agents, restarts, recipients and time | F3, F5, F8 | M | General multi-agent orchestration |

These 28 entries are a **starter set**, not 28 independent proof families, not exhaustive, and not claims of established results. Keep taxonomy mapping separate from our proposed scenarios. Some catalog rows intentionally overlap: they are different operational threat models for reusable machinery.

## 5. What counts as a scenario-specific "checker"?

Each scenario produces a bundle, not merely a unit test and not merely a theorem:

1. **Threat spec:** trustworthy formalization of the intended real-world bad event; attacker capabilities, target resources, horizon, receiver/observer inputs, permitted effects.
2. **Executable policy:** a trusted *pre-action* gateway where necessary; precise allowlists or safe-state predicates. If it cannot mediate a class of actions, state that as a gap.
3. **Formal statement:** Lean predicate(s) over traces/states/probability distributions and a proof over the specified adversary class.
4. **Configuration checker:** exact cardinalities, path rules, permissions, budgets, invariants or certificates, rejecting invalid/unprovable configurations. No float approximation where integer arithmetic suffices.
5. **Implementation correspondence:** link the real binary/runtime/OS isolation and trusted infrastructure to the formal transition system; unresolved environmental properties remain assumptions.
6. **Falsification tests:** adversarial mutation, concurrency, crashes, repeated trials, cross-episode recovery, alternate IPC and bypasses, negative examples intended to fail.
7. **Usefulness and evaluation:** honest task completion, cost, interruption/defer and latency, contrasted with unrestricted baseline. The null policy ("block everything") must not be rewarded as a practical success.
8. **Assurance manifest:** hashes/versions, supported attacker model, verified theorem, tested correspondence, residual assumptions, evaluated threat families, independent reviewers, deployment claim and failure cases.

A proof of "the checker accepts only values it accepts" is circular. Require a separate *statement-fidelity review*: prove the formal predicate captures the identified catastrophe or say precisely what narrower claim it establishes.

### Required evidence levels (do not conflate)

- SPECIFIED — a readable threat model and desired property.
- THEOREM_VERIFIED — the stated Lean theorem kernel-checks with approved axioms.
- IMPLEMENTATION_MODELED — a formal program/state machine satisfies an invariant.
- CORRESPONDENCE_TESTED — executable traces observed to refine the abstract transition model in stated tested environments; tests do not prove all inputs.
- ENVIRONMENT_ENFORCED — trusted operating-system/control-plane boundary blocks the relevant bypass classes in the claimed environment, with identified residual assumptions.
- EMPIRICALLY_EVALUATED — selected adversarial and honest-task experiments, confidence intervals only when sampling assumptions hold.
- DEPLOYMENT_ASSURED — **only for one exact narrowly scoped scenario, configuration, horizon and threat model**, after independent review of all obligations. Never infer this automatically from a list of green CI jobs.

The existing 44 empirical certificate manifests are conditional artifacts, **not** 44 independently deployed scenario checkers. Their 0 deployment-grade status is appropriately conservative. They can be linked as evidence under F6.

## 6. Starter machine-readable scenario schema (proposal)

A directory such as scenarios/SC-01/ could contain:

- scenario.yaml — stable ID, references, source setting, catastrophe predicate in plain language, attacker controls, target asset, protected operations, runtime configuration, receiver/side information, secret lifetime/horizon, baseline usefulness target.
- claim.lean — formal statement and proof, with named premises; import shared F1–F8 modules.
- policy.json or policy.py — trusted gateway configuration to which the claim refers.
- correspondence.md — for every premise, concrete enforcement, evidence, unresolved assumption and relevant component/hash.
- tests/ — both positive use-cases and negative exploit cases (including failed/bypassed designs).
- manifest.json — evidence ledger and exact CI/build artifact hashes, severity of remaining blockers.
- result.md — plain-English conclusion with scope, falsifiable tests, limitations and next experiment.

Proposed required scenario fields (semantic requirements, not a finalized parser):

  id, title, sources, threat_origin, attacker_controlled,
  protected_assets, harmful_transition_or_event,
  runtime_boundary, permitted_actions, forbidden_actions,
  complete_receiver_observations, secret_side_information,
  horizon_and_persistent_state, honest_task_distribution,
  theorem_name, theorem_assumptions, trusted_computing_base,
  checkers, implementation_hashes, negative_tests,
  usefulness_metrics, environment_evidence, unresolved,
  status, reviewer_decisions.

Implement schema validation with fail-closed missing required fields. Avoid allowing a generator to declare its own evidence as verified.

## 7. Selection and experimentation process

**Do not cherry-pick a scenario solely because an easy but unhelpful theorem is available.** Prioritize:

- Plausible high-impact harm and relevance to real agent deployments.
- An objectively observable/reproducible bad action or state (not vague intent).
- A narrow gateway/invariant that still permits valuable honest work.
- A small trusted computing base with genuine authority over the action.
- A correspondence argument and failure tests that could falsify it.
- Reusability: proving the invariant would unlock several other catalog rows.

### Suggested progression

**Wave 0, finish the present slice — SC-01 + SC-02 + SC-04:**
- Repair the scope: *exact uniform-secret recovery*, not generic collusion prevention; include receiver side information and secret/episode lifetime.
- Demonstrate 2-episode 32-bit reconstruction against the original budget; implement cumulative accounting or valid reset.
- Fix mutable channel config, integer cardinality, frozen delivery, diagnostic and clock observability.
- Run a separated two-process sandbox and establish trace correspondence; mandatory Lean CI; obtain useful main-task measurements.
- Mark the claim conditional until *all* receiver-observable paths are bounded.

**Wave 1, same harness, more structural properties — SC-03 + SC-08 + SC-09 + SC-13 + SC-25:**
- Deny unapproved network egress, process execution, privilege escalation and control-plane tampering; establish "check before effect" and absorbing shutdown.
- Ground action classes in BashArena and a few LinuxArena side tasks. Construct a shared pre-execution event trace checker.
- Compare honest task success and identify which permissions must be reintroduced under typed/trusted authorization.

**Wave 2, artifact controls — SC-16 + SC-17 + SC-18 + SC-21:**
- Introduce hash-locked change review, permission graph invariants and a transactional deploy/apply gate.
- Reuse the same state machine and F4 provenance checker for code/infra/evaluation changes.
- Validate on ControlArena async sabotage settings and measure whether tight controls impede legitimate work.

**Wave 3, harder semantics — SC-15 + SC-20 + SC-22 + SC-24:**
- Treat broad backdoors, poisoning, deceptive research summaries and monitor collusion as conditional safety cases requiring empirical coverage or trusted independent judgment.
- Formalize only the narrower properties for which premise evidence is available; explicitly document impossibility or missing-observation results.

Successes remain in the library. Failed candidate safeguards remain documented as **negative results**; a failed scenario need not terminate the overall program.

### Scenario scorecard (for choosing the next one)

Record threat relevance, formal tractability, runtime-enforcement tractability, coverage completeness, likely honest utility, cost of evidence, and expected reusability. Prefer a *Pareto frontier* over an arbitrary weighted scalar.

For every candidate, answer:
- What concrete adversarial trace falsifies the safety statement?
- Can the attacker realize that trace *without* calling the trusted gateway?
- Would a perfectly malicious, arbitrarily capable model violate the claim under the declared interface?
- Can two agents/episodes combine permitted actions into a forbidden outcome?
- Does the certified bad event actually correspond to the harm we care about?
- Which approved honest task is still achievable, with what completion rate?
- Does evidence come from a frozen evaluation, independent implementation check, or merely a second LLM reviewer?
- What would a skeptical external AI-control researcher reject first?

## 8. Observations and cautionary lessons from this review

1. **The proof may be correct while the safety case is false.** A receiver seeing only V is a serious environmental claim; testing one Python method does not discharge it.
2. **Formalization has a judgment bottleneck at the statement boundary.** Model judges can cheaply propose counterexamples and critique assumptions, but independent expert review remains useful at scenario selection and promotion.
3. **The attacker's *complete feasible action set* matters more than benchmark average attack success.** The reference monitor should structurally remove forbidden bad classes when possible, rather than trying to sample every possible attack.
4. **Explicit time and order matter.** A perfect monitor acting after irreversible damage may be useless; synchronous and asynchronous settings require different safety predicates.
5. **Effects accumulate.** Cross-episode memory, repeated low-bandwidth messages, duplicated workers and restarting counters are composition attacks.
6. **Leakage cardinality != "no coordination".** Even one bit can coordinate a bad action. To prevent an action, control the action; use bounded communications to support only the narrower recoverability claim.
7. **Null/rejection/logging/timing are possible outputs.** A "fixed schema" cannot be assumed to be the complete observation interface until the harness makes it so.
8. **Use exact arithmetic for exact obligations.** Integer transcript cardinalities and resource budgets do not need floating log comparisons.
9. **A modeled sandbox or Lean gateway is not the deployed executable.** Require a real OS/process boundary and a credible refinement/verification story.
10. **Usefulness is not optional.** Blocking all actions can trivially satisfy many invariants; report task success, cost and false intervention side by side.
11. **Fail-open system components dominate theorem elegance.** Trusted tool APIs, configuration mutation, filesystem overlays, IPC, release gate and CI/provenance deserve adversarial attention.
12. **Risk certificates based on population-average ROC do not imply adaptive per-submission guarantees.** The existing ComposeBlindSpot negative result should be an explicit lint rule in any certificate promotion.
13. **Benchmarks are opportunity generators, not exhaustive taxonomies.** Start with Redwood/AISI/Google, broaden with MITRE ATLAS, and document gaps.
14. **Prefer a finite set of reusable proof families** applied to many distinct situations, rather than separate hand-written, incomparable theorems.
15. **Preserve counterexamples and unsupported scenarios.** Failure to make a scenario tractable or useful is information, not an incentive to relabel assumptions.

## 9. Request for a separate Claude-session review

Read this file and [reviews/covert-channel-gateway-review-2026-10-07.md](reviews/covert-channel-gateway-review-2026-10-07.md). In addition to the gateway objections, independently challenge the scenario taxonomy:

- Which high-stakes classes are missing or redundantly listed?
- Which H-feasibility ratings are too optimistic because side channels, capability delegation, TOCTOU, process isolation or recipient memory defeat them?
- Do the proposed checker families have a sound generic abstraction that actually improves evidence reuse?
- What are the strongest formal *no-go* results or impossibility conditions worth verifying?
- Is Wave 1 preferable to finishing SC-01, or should another scenario become the first end-to-end deployable artifact?
- Can legitimate SWE work still be completed under these restrictions? Demand concrete honest-task baselines.
- Which proposed theorem goals confuse "bounded observation" with confidentiality, safety or coordination prevention?
- Are there nearer public projects with verified reference monitors, noninterference, sandboxing or AI-control scaffolds that should be reused rather than rewritten?

Reply in a *new* file under reviews/dialogue/claude-01.md or the next Claude-numbered round, cite latest commit SHAs, and end with DIALOGUE_STATUS: CONTINUE or DONE. Don't silently modify the reviewer-authored catalog while rebutting it. Consult the user before claims of deployment readiness. The conversation does **not** run autonomously because files are present.

## 10. Source references and evidence boundaries

Research/taxonomies:
1. Redwood Research, *BashArena and Control Setting Design*, 2025-12-18: https://www.redwoodresearch.org/blog/basharena-and-control-setting-design
2. Redwood Research, *Introducing LinuxArena*, 2026-04-20: https://www.redwoodresearch.org/blog/introducing-linuxarena
3. LinuxArena project: https://www.linuxarena.ai/
4. AISI/Redwood ControlArena settings: https://control-arena.aisi.org.uk/settings/
5. AISI/Redwood ControlArena overview: https://control-arena.aisi.org.uk/
6. Google DeepMind, *GDM AI Control Roadmap*, 2026-07: https://arxiv.org/abs/2607.13087
7. Google DeepMind, *Securing the future of AI agents*, 2026-06-18: https://deepmind.google/blog/securing-the-future-of-ai-agents/
8. MITRE ATLAS taxonomy: https://atlas.mitre.org/
9. MITRE ATLAS data: https://github.com/mitre-atlas/atlas-data

Local materials:
- CovertChannel counting proof and design point: [ControlStack/CovertChannel.lean](ControlStack/CovertChannel.lean)
- Gateway implementation/tests: [gateway/](gateway/)
- Gateway theorem/implementation bridge: [gateway/CORRESPONDENCE.md](gateway/CORRESPONDENCE.md)
- Gateway adversarial review, P0/P1 defects, CI caveat: [reviews/covert-channel-gateway-review-2026-10-07.md](reviews/covert-channel-gateway-review-2026-10-07.md)
- Conditional empirical certificate statuses: [assurance/](assurance/) and [ROADMAP.md](ROADMAP.md)

**This catalog is a research plan.** It makes no claim of 28 solved scenarios, comprehensive coverage, sound implementation refinement, or deployment-grade assurance. External sources support the threat inventory and evaluation settings, while proof/checker constructions and rankings are original proposals to be validated.
