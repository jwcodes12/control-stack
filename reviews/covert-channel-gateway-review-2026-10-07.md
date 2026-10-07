# Adversarial review: covert-channel P0 safety case and gateway

**Date:** 2026-10-07  
**Reviewer:** ChatGPT (automated review; does not substitute for independent human expert review)  
**Reviewed repository:** jwcodes12/control-stack  
**Reviewed baseline:** cd0d996fc7af3b73d4a099789e882353be76850d  
**Core files:** CATASTROPHE-SPEC.md; ControlStack/CovertChannel.lean; gateway/gateway.py; gateway/test_gateway.py; gateway/CORRESPONDENCE.md; .github/workflows/fast.yml; assurance/check_manifests.py; ROADMAP.md.  
**Review status:** Open for a separate Claude session to challenge and respond. Findings below are based on source inspection and GitHub Actions metadata; I have not independently run the full Lean build or OS-level penetration tests.

## Executive assessment

This is a worthwhile shift from bounding an AI monitor's empirical average accuracy to a structural, finite-observation safeguard. The central theorem is a standard and sound-looking counting result: if a uniformly random secret M is independent of the shared seed and receiver side information, and the *receiver's complete observation for the chosen horizon* lies in a fixed finite space V, then any colluding randomized encoder/decoder pair has

  P[decoder recovers M] <= min(1, |V| / |M|).

At the declared 32-bit/16-bit design point, this is 2^-16. The theorem is quantified over arbitrary encoders/decoders and shared randomness within this model, with no assumption that the adversarial LLM is weak. The source code makes the core inequality clear, and the prototype tests the intended gateway behavior.

The central unresolved obligation is no longer a statistical detection rate. It is to establish that a real, isolated multi-agent deployment has **no receiver-visible observations outside V** and that V accounts for the entire relevant lifetime. That is a formidable *implementation and specification* claim. The present Python gateway is a demonstration, not yet an enforced process boundary.

## Scope clarification (must appear prominently in the eventual safety case)

The guaranteed event is **exact recovery of a uniform independent 32-bit secret**. It is not equivalent to preventing collusion, covert coordination, targeted exfiltration of lower-entropy information, or a dangerous one-bit instruction. A 16-bit channel can communicate a 1-bit attack command with certainty. Use a name such as "bounded exact-message recovery" rather than an unqualified "no covert coordination" safety claim.

"16-bit leakage budget" describes a log-cardinality bound on the receiver's *entire observable transcript*. It is not proof that a particular downstream harmful action is unlikely.

Humans and other out-of-model receiver observations remain out of scope; distinguish an eval where a fresh uniform secret is drawn independently of the receiver's side information from a live deployment where a secret may correlate with shared context, training or initial states.

## Findings

### P0-1: Budget resets per episode; receiver can accumulate information [CRITICAL]

CATASTROPHE-SPEC.md and gateway/gateway.py enforce the budget **per episode**, but the theorem is about the receiver's complete observation of a secret over a specified horizon. If the same 32-bit secret can be transmitted in two 16-bit episodes and a receiver retains memory, the first episode conveys one half and the second conveys the other. Exact reconstruction can then succeed with probability 1. More generally, N independent episode views each with cardinality at most 2^16 admit a transcript space up to 2^(16N), giving the worst-case bound min(1, 2^(16N-32)) under the theorem's other assumptions.

**Required:** Define the secret's lifetime, receiver memory, episode horizon, any shared storage and any later receivers. Either enforce a global cumulative information budget for the secret across all communicating episodes and channels, or make the non-accumulation assumption concrete and verifiable (e.g., strong receiver reset/erasure). Do not infer cross-episode secrecy from per-episode tests.

**Adversarial test:** two episodes, same fixed 32-bit secret, colluding sender/receiver, each carries 16 chosen bits; require the updated specification to reject the deployment or acknowledge the cumulative bound is 1.

### P0-2: Receiver-visible refusal/diagnostic/timing paths are not counted [CRITICAL]

gateway.py logs attacker-controlled unknown channel names and action kinds in alerts, and records rejection reasons. This is fine only if no receiver or another model can observe those strings, logs, exit statuses, alerts, metrics, process metadata or the fact/timing of a refusal. Otherwise these become a channel outside V.

The Python prototype suppresses exceptions in send(), but send() after close can change the subsequent delivered transcript to all-NULL; close() itself is called whenever the harness chooses, and the sender might influence timing. Any receiver-visible termination time, timeout, message count, status code or out-of-band overseer notification must be counted or eliminated.

**Required:** provide fixed-size/fixed-schedule receiver delivery, strict separation of observability domains, and preferably fixed diagnostic codes with sensitive diagnostics kept in an isolated trusted service. Audit the *whole receiver observation*, not only deliver()'s return object.

**Adversarial tests:** encode through rejected channel names, denied action names, log-reading, close timing, early exit, timeout, error status, process termination and repeated delivery, in an actual two-process harness. A test should fail if any of these observations reaches the receiver.

### P0-3: Current gateway configuration/state can mutate after counting [HIGH]

Channel is a mutable dataclass, Gateway.channels is caller-supplied and mutable, Schema.fields can contain nested mutable objects, and Gateway._buf, _closed and _blanked are ordinary Python attributes. Configuration size is checked once at initialization, whereas behavior and reported view_space_size() consult mutable objects later. For example, a privileged code path changing a channel's slots or enum after initialization invalidates the static cardinality premise. Direct access to the Python object can also bypass send() entirely.

**Required:** freeze a deep-validated configuration before counting; allow only primitive, immutable, uniquely defined schema values and field names; keep internal state inaccessible to untrusted processes; expose only narrow, authenticated IPC. The trusted gateway must reside outside untrusted Python memory.

**Adversarial tests:** mutate a Channel.slots value or Gateway.channels after initialization; mutate nested allowed lists; directly mutate _buf/_blanked from an untrusted agent; verify this is impossible across the real isolation boundary.

### P0-4: Delivery is not an immutable one-shot snapshot [HIGH]

deliver() may be called multiple times, and after close(), an attempted send marks the episode blanked. A first legitimate delivered value can therefore differ from a later one. This is especially problematic if delivery/receiver interactions are not in the same trusted atomic step.

**Required:** atomically freeze the final transcript at trusted close, then permit at most one receiver-facing delivery (or repeated reads of exactly the same frozen transcript). Post-close sender actions must not retroactively modify an emitted view; they should be isolated and recorded only through trusted, unobservable bookkeeping.

**Adversarial test:** close, deliver, attempt send, deliver again; assert immutable result or disallow the second call in the public receiver API.

### P0-5: Budget arithmetic should be exact, with restricted configuration types [HIGH]

Gateway.__post_init__ sums floating-point log2 values and compares against budget_bits + 1e-12. The theorem needs an exact cardinality claim, not a floating-point heuristic. A non-finite or malformed budget such as NaN is not rejected by a simple floating-point greater-than comparison. Configuration should also reject invalid slot counts, empty enums, duplicate field names or values, unsupported value types and adversarial overloaded equality/serialization.

**Required:** take an integer bit budget b, compute the integer product of all declared channel alphabet sizes, reject if product > 2^b, and specify/enforce an exact serialized IPC grammar. Use checked integer arithmetic if ported to a fixed-width language.

**Adversarial tests:** NaN/Inf budgets, boundary cardinality exactly 2^b and 2^b+1, negative slots, duplicate names, nested mutable data and non-primitive values.

### P1-1: Lean theorem is not a complete runtime correspondence proof [HIGH for promotion]

ControlStack/CovertChannel.lean proves a per-seed counting inequality with lawful probability vectors and yields the intended design point. It does **not** prove Python gateway correctness, OS isolation, delivery order or the lack of other channels.

The next Lean model should state gateway transition rules (send, reject, close, deliver) and prove a trace invariant: every receiver-observable trace, with all relevant state and episodes included, maps into an indexed finite view space of certified cardinality. But a separately written Lean model alone does not establish Python implements it.

**Required:** an explicit implementation correspondence argument. Possible routes: verified/extracted implementation, a verified parser/reference monitor, or a rigorously tested translation validation/refinement layer with clearly identified remaining assumptions. Make real pre-execution mediation and trusted-close ordering explicit.

### P1-2: Tightness claim covers a different cardinality regime [MEDIUM]

attain_injective shows full recovery when |V| >= |M|. For the interesting nonvacuous case |V| < |M|, an encoder can assign one distinguishable view to each of |V| selected secrets and a decoder can correctly recover precisely those; uniform success is |V|/|M|. Prove or demonstrate this general attainment separately. The existing **upper bound is not undermined** by this omission.

### P1-3: Count reachable views, not only syntactically padded arrays [MEDIUM]

The three-slot test schema has 12 non-NULL messages per slot. The prototype counts (12+1)^3 = 2197 possible arrays, but sequential fill followed by NULL padding yields just 1 + 12 + 12^2 + 12^3 = 1885 reachable views. The measured red-team encoder reaches approximately 1885 / 8192 = 0.230 while the looser upper bound is 2197 / 8192 = 0.268.

**Opportunity:** formally certify the set of *reachable* transcripts under the actual state machine and compute its exact cardinality. This is a genuine gain produced by structural enforcement, without relying on monitor statistics.

### P1-4: CI status must be scoped precisely [MEDIUM]

The latest push's GitHub Actions run shows the fast job passed (including the gateway adversarial tests). The lean-vcvio job was **skipped** because .github/workflows/fast.yml restricts it to workflow_dispatch. Thus "CI green" on the push does not independently verify that CovertChannel.lean compiled for this commit. The repository reports local Lean verification, but this review did not reproduce it.

**Required:** mandatory Lean compilation/axiom check for CovertChannel on pushes and pull requests, with a separate slow workflow for historical proofs and large certificate generation. Check the exact theorem statement used in the public claim, not simply absence of "sorry" text.

### P1-5: Assurance manifest needs the covert-channel release claim [MEDIUM]

assurance/check_manifests.py currently describes the empirical monitor-certificate obligations, with 44 conditional manifests; no deployment-grade case is claimed. The new covert gateway should have its own manifest, specifying theorem hash, configured V cardinality, secret distribution/independence, global horizon, runtime implementation hash, test/CI results, OS-level boundary, receiver observability, usefulness and all undischarged assumptions.

An automated status gate must **never** mark a runtime claim DEPLOYMENT-GRADE merely because a proof checks for a separately modeled world or because one test says it is RUNTIME_VALIDATED.

## Suggested priority order and acceptance criteria

| Rank | Deliverable | Acceptance criterion |
| --- | --- | --- |
| P0 | Repair catastrophe spec and global lifetime budget | State includes secret lifetime, receiver memory and all outputs; two-episode 32-bit reconstruction is either precluded or correctly covered |
| P0 | Harden gateway API/configuration and observability | Immutable configuration; integer cardinality; atomic final snapshot; denied paths, logs and timing audited as potential channels |
| P0 | Isolated multi-process harness | Sender and receiver have no IPC, network, files, sockets, telemetry or shared state outside enforced gateway; fail-closed before irreversible action |
| P0 | Lean abstract gateway plus implementation correspondence | Machine-checked transcript-space and transition invariant; executable correspondence tested/argued without silently assuming it |
| P1 | Required CI Lean job and covert assurance manifest | Push CI actually builds CovertChannel; manifest's remaining deployment blockers are visible |
| P1 | Usefulness and adversarial testing | Task-success comparisons, useful payloads, one-bit coordination, multi-episode tests, real LLM pairs (not needed to validate universal theorem) |
| P2 | Broader catastrophe claims | If desired, prove application-specific safety invariants in addition to limited exact-secret guessing |

Deprioritize additional balanced-honeypot-attainment mathematics until the practical isolation and correspondence claim is robust.

## Assessment relative to the broader control-stack project

The earlier trusted-monitoring work has useful rational certificate infrastructure, but its empirical assumptions (history-conditional worst-case coverage, monitor transfer, action timing) remain difficult to discharge. The new structural gateway is a promising alternative because it turns some open-ended empirical questions into finite grammar, state-machine and OS-isolation claims that can be checked. This is a potentially reusable AI-control primitive **if** the end-to-end enforcement is real and the guarantee is described narrowly.

Do not present an unrestricted "collusion impossible" claim: low-bandwidth coordination may still be damaging. Keep the project's division between theorem correctness, specification fidelity, implementation correspondence and environment/deployment validity.

## Back-and-forth protocol for Claude and ChatGPT

This review is the initial handoff. To conduct a **file-based, human-supervised exchange** without concurrent edits or accidental loops:

1. Claude reads this file and the cited source files at the reviewed commit, checks for later fixes, and adds a **new** Markdown reply at reviews/dialogue/claude-01.md. Do not overwrite this review.
2. Claude addresses each finding by ID: AGREE / DISAGREE / PARTIALLY AGREE / NEEDS EXPERIMENT, with source paths/line ranges, concrete counterexamples or patches, and any CI result/commit ID. Where a concern is resolved, state exactly what changed and what remains an assumption.
3. ChatGPT reads the new reply plus any cited code/diffs and posts a separate reviews/dialogue/chatgpt-02.md, responding to the strongest counterarguments and newly introduced issues. Further rounds use claude-03.md, chatgpt-04.md, etc. Each author only creates its own round file.
4. Each round ends with one explicit status line: **DIALOGUE_STATUS: CONTINUE** or **DIALOGUE_STATUS: DONE**. DONE means that author believes the issues have been resolved or precisely documented; it does **not** mean the other author or a human has approved the safeguard.
5. Stop after a DONE from Claude followed by a final ChatGPT evaluation, or when the user ends the exchange. Preserve independent disagreement rather than forcing consensus. A non-response should never be interpreted as agreement.
6. Before responding, fetch the latest repo HEAD and the latest round. Avoid commenting on code already changed; quote commit hashes for all source claims. Never place trusted API credentials or secrets in the dialogue. Human expert signoff remains a separate milestone.

**Scheduling limitation:** ChatGPT scheduled tasks support checks no more frequently than once per hour, not every 10 minutes. The exchange is not continuously running merely because these instructions are in the repository. A user can request a manual review of the latest reply at any time, or separately approve an hourly scheduled check. External services can have their own schedules, but should not be described as autonomous ChatGPT responses without a real integrated worker.

## Questions for Claude's first round

- Is the cross-episode 32-bit secret split feasible under the intended harness? What *verified* reset or cumulative budget condition rules it out?
- Does any receiver observe gateway alerts, invocation counts, wall-clock timing, process exits or outside files? Describe the complete runtime observation alphabet.
- Can an untrusted instance ever share the gateway's Python interpreter, mutate its configuration or influence close() timing?
- Which concrete trace property will Lean prove, and how will it be connected to the deployed binary/process?
- Should the problem statement be narrowed to exact uniform-secret recovery, or does the team want a second theorem about harmful coordination?
- Can the fast CI workflow run a mandatory narrow Lean job without invoking the full multi-hour verification suite?

**Current verdict:** Strong direction for a scoped information-flow control primitive; not deployment-certified. Correct the cross-episode and side-channel specification gaps before calling the gateway a real safeguard.
