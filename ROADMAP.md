# ROADMAP: control-stack status (kept current; last updated 2026-10-08 evening: circle effort, primitives, adversarial review, VM link fix)

## SC-01 statement review and runtime-candidate audit (2026-10-08)

Read-only verification [Actions #37880911299](https://github.com/jwcodes12/control-stack/actions/runs/37880911299) successfully validated 20,719 independently specified bounded Python gateway traces, three fail-closed AST receiver-field checks, ordinary gateway/ledger test replay and VM host-capability inspection. The finite-state checks **do not** establish universal Lean-to-OS refinement or full receiver-observation coverage. They detect modeled transition mismatches and obvious source-level receiver-field regressions.

**Prospective native acceleration:** a privileged x86 runner reported KVM API version 12 in [read-only host check #37881180806](https://github.com/jwcodes12/control-stack/actions/runs/37881180806). A paused image-free x86 QEMU [reported KVM enabled in #37881258339](https://github.com/jwcodes12/control-stack/actions/runs/37881258339). This is a potential **x86 guest port**, not acceleration of the current aarch64 images and not a new usefulness trial. [Port/acceptance plan](reviews/assurance-priorities/host-port-readiness.md).

**Usefulness has not recovered:** archived QEMU TCG 0.25-second SC-01 receipts remain 0/64 completed lifetimes in both conditions, with 640 sender and 640 receiver invocations timed out across conditions. The GitHub-hosted ARM64 runner had no `/dev/kvm`; x86_64 was not usable for the pinned ARM64 guests and the unprivileged KVM probe returned `PermissionError`. No new guest pair was provisioned and no live side-channel/usefulness experiment was run. A permitted native ARM64 KVM host, or an independently preregistered amended protocol, is still required before rerunning usefulness. Even a passing usefulness result would leave full receiver-observation correspondence open.

**Statement-review boundary:** a documented adversarial second pass enumerates quantifiers, load-bearing assumptions and unproved runtime refinements for SC-01, leakage, HALT, gating, leases and composition. It is **not independent external review** and grants no assurance promotion. See [detailed audit](reviews/assurance-priorities/theorem-statement-and-runtime-audit.md).


## Independently rebuilt original A/B/C integration (2026-10-08)

The three original branches A, B, C passed separate pinned-root Lean builds and their source-branch scenario checkers (A 8/B 7/C 7 Python tests). B's 28 original claim files compiled independently. Original C `THEOREM-REGISTRY.md` was stale; the merged generator repaired this without altering C. The merged work branch now contains 865 source-indexed declarations, 34 new conservative source-scope annotations and 821 still unreviewed `UNKNOWN` adversary classifications. The expanded HALT delivery model compiled with standard-only axioms; scheduler fairness and concrete HALT implementation remain outside the proof. See [comparison](reviews/structure-merge/comparison.md) and [scope audit](reviews/structure-merge/theorem-scope-audit.md).

## Candidate hardening follow-up (structure-merge-20261008-gpt6-finish)

The original work branch has continued evolving. This separate candidate preserves its existing validated-source inventory while expanding **all 28 scenario manifests** to cover named per-premise usefulness status and six explicit scope-assumption axes: threat coverage, runtime correspondence, environment, lifetime/composition, usefulness and independent review. Missing axes and an unsupported self-asserted `SUPPORTED` scope status are rejected by the static checker. This is schema-level diligence only and must not be presented as new Lean or runtime validation.

SC-01's original shared-cache and frozen VM usefulness refutations remain recorded. Other case usefulness statuses are `NOT_RUN` unless separately grounded. All new preregistration drafts/templates are in [prereg/](prereg/); historical root `PREREG-*.md` files remain frozen. The independent [validation addendum](reviews/structure-merge/hardening-validation.md) records what was and was not executed in this environment.

## Canonical structure-merge status

This is the **single status entry point**. The source-derived scenario index is [scenarios/INDEX.md](scenarios/INDEX.md), and the source-derived theorem registry is [THEOREM-REGISTRY.md](THEOREM-REGISTRY.md). Their status fields are not deployment assurance. The independent comparison is [reviews/structure-merge/comparison.md](reviews/structure-merge/comparison.md).

### Structure integration (work branch; build acceptance PASS, operational assurance pending)

**Conditional shutdown theory extension:** `ControlStack/HaltLiveness.lean` passed pinned Lean 4.34.0 on [CI #37877045361](https://github.com/jwcodes12/control-stack/actions/runs/37877045361), with four standard-only axiom reports. The trusted HALT-delivery premise remains an unverified scheduler/runtime obligation, so this is **not liveness assurance for a deployed agent**.

[CI #37870787641](https://github.com/jwcodes12/control-stack/actions/runs/37870787641) passed pinned Lean compilation, 28/28 scenario claim elaborations, 8 printed standard-only axiom reports, 18 mutation tests, 4 certifier tests and generated-index checks. Original SC-01 case steps 1–4 passed; phase 5 correctly identified a frozen receipt's host-bound OpenSSL mismatch. This is **not** an independent applicability or deployment validation.

- SC-01, SC-03 and SC-13 have named proof references and remain **conditional**, not deployment assured; SC-27 remains **draft** because audit-dispatch integrity does not prove independently attested evidence.
- 28 scenario folders exist: **3 conditional, 25 draft**. A scenario folder is not a tested safety case.
- Reviewed main proof definitions now live under `ControlStack/Core/`, `ControlStack/Families/` and `ControlStack/Witnesses/`, with old imports preserved. C contributes policy-tamper and shared-state gate candidate proofs.
- The theorem registry is a lexical source inventory (865 declarations after CI regeneration), not a Lean-kernel result for the merged branch. Unknown adversary/premise mappings are kept unknown; no artificial novelty claims.
- **Build/integration acceptance passed** in CI #37870787641. Remaining before operational approval: independent model-to-runtime correspondence review, complete threat observability/provenance, negative trials, and a separately approved viable SC-01 protocol. The historical OpenSSL receipt remains frozen and cannot be replayed as a new host's valid receipt.
- C's four active-bundle observations were reconciled conservatively: SC-01's frozen VM usefulness gate and single-host side-channel gate failed; SC-03 proves only a narrow immediate-peer model; SC-13 assumes exclusive trusted dispatch; SC-27 still lacks independently rooted attestation.

The older time-stamped results below are **historical**, not a new successful verification of this work branch.


What is done, what is in flight, and what is left. Per-result detail (assumptions, scope, review history) is in
[STACK.md](STACK.md); this file is the one-page plan.

Status legend:
- ✅ **verified**: a frozen ledger statement whose proof passed the Lean gate (standard axioms only), after a red team
  by two foreign model families and an orchestrator fidelity audit;
- ✅ **proved**: a VCVio-level file checked with `lake env lean` and `#print axioms` (not ledger-gated);
- 🔄 in progress;
- ⏳ planned;
- 🔒 blocked on a decision by John.

## Status at a glance — 2026-10-08 (evening)

- **SC-01 (selected scenario).** Theory complete for a bounded interface, including stateful side channels with
  feedback (`Leakage`).
  - Single host: usefulness 320/320, but the side certificate is REFUTED (checker exit 3).
  - QEMU pair ([VM status](gateway/vm/STATUS.md)):
    - Link race fixed: QEMU `socket,connect=` never retries; the listener now starts first and the pair is required
      to be ESTABLISHED. Config `56a4dfa1` is unchanged; 8/8 health; 10/10 controls.
    - The frozen usefulness gate FAILED (0/64 in both conditions): all 640 agent runs exceeded the 0.25 s deadline
      under TCG emulation.
  - 🔒 Owner decision: a preregistered deadline amendment, or hardware isolation. Either way the probability bound
    stays a separate obligation (`gateway/vm/BOUND.md`).
- **Primitives.** Every family F1–F8 now has at least a proved model: shared `Gate`, F4 artefact, F7 approval,
  F5 leases, absorbing halt. F4, F5 and F7 have no runtime implementation. See
  [PRIMITIVES-AND-SCENARIOS.md](PRIMITIVES-AND-SCENARIOS.md).
- **Review status.**
  - The new Lean (Leakage, Necessity, Gate, GateClients, Lease, LeakWitness) is proved, with standard axioms only.
  - Adversarially reviewed by Gemini 3.1 Pro and Opus 5.5 (same family as the author). All substantive findings are
    fixed or documented: [disposition](reviews/adversarial-2026-10-08/disposition.md).
  - NOT ledger-verified. The proofledger foreign-family red team plus Lean `Witness` is the recommended next gate,
    for statements rather than proofs.
- **Next.** Work that needs no testing is planned in [STRUCTURE-PLAN.md](STRUCTURE-PLAN.md): scenario folders, a
  generic case checker, a theorem registry, adversary classes and gap-closing theory.
  1. Owner: SC-01 deadline or hardware.
  2. Proofledger red team of the headline statements, with Sol/Astra and Gemini as foreign families.
  3. Runtime F4/F7 implementations with correspondence tests.
  4. Wave 1 on BashArena (SC-08/09/13/25).
  5. Open F6 theory: a positive policy under false positives, imperfect auditors, adaptive coverage, collusion plus
     side channel.
  6. Human expert review (🔒).

## SC-03 egress update (2026-10-08)

Implemented test-only launcher/gateway/adapter, actual namespace validator, host packet and syscall observers,
pinned dependency install/compile/test, 62 passing full-suite controls, three successful mutation checks,
nine oracle regressions, and six standalone Lean theorem checks (the original full `lake build ControlStack` passed).
See `egress/README.md`, `egress/results/summary.json`, `egress/FIDELITY.md` and `assurance/egress-boundary-v1.json`.
Reachability only; CONDITIONAL; no production deployment. Auditgate untouched.
Astra and approved Opus 5.5 reviews produced oracle fixes. Next: all-destination process attribution in a
isolated disposable outer topology; the egress GitHub workflow now passes.
The authorized follow-up after 09:30:31 UTC fixed IPv6 trace/fragment observer bugs and
refreshed full/mutation receipts. A bounded loopback-only outer-namespace experiment passed:
eight initial TCP/UDP transmissions, two independently traced sender PIDs, zero drops,
missing-trace mutation detected. General attribution remains unresolved; next is integrating
the gateway/sandbox into that isolated topology. See `reviews/egress-follow-up-2026-10-08.md`.
No rate-limit error occurred; account reset time remains unavailable. Private branch `egress-r10-controls` is published (2026-10-08). [Egress CI](https://github.com/jwcodes12/control-stack/actions/runs/37784398180) passed on `b30177e`: 62/62 controls, three mutations, zero packet drops and six Lean theorem checks. Git pushes and CI are authorized; direct messages to people still require approval.

## Circle effort (2026-10-08)

Consultation: `reviews/circle-consult-2026-10-08/`. Astra (gpt-6-astra, xhigh) and Fable (claude-fable-5-1) reviewed
adversarially. Both said not to build a general certificate calculus now, because its combinators are classical. The
value they see is conditional accounting, refutation and experiment design. Remaining work across all primitives and
scenarios: [PRIMITIVES-AND-SCENARIOS.md](PRIMITIVES-AND-SCENARIOS.md). Witness scopes:
[NECESSITY.md](NECESSITY.md).

| item | what it gives | status |
|---|---|---|
| `Leakage.lean` | one leakage-transfer principle: an adversary informed through dominated, history-dependent kernels is worth ≤ mass(c) blind adversaries. Instances: `covert_seq`/`covert_side_bound`/`sc01_adaptive_target` (side channels with state and feedback; replaces `dom_pi`'s independence premise); `audit_leak_bound`/`audit_leak_prod` (leakage-sensitive adaptive auditing; catch flags are free, `cval_live`); `audit_adaptive_hidden` (adaptive attackers gain nothing against a hidden random schedule, formalising AuditBudget's remark) | ✅ proved; after review: support-restricted `audit_leak_bound` (hypotheses only on size-B schedules), `covert_seq_seed` (seed-dependent certificates), corrected `survInd` prose. Informative only near "no side channel" at the SC-01 design point (~0.15 bits over 5 episodes) |
| `Necessity.lean` | witnesses: seed-correlated secret (strict for \|M\| ≥ 2, bridged to `successProb`), correlated lifetimes break the gate (9/10 vs 1/80), marginal side certificates do not compose; plus a policy comparison (first-come auditing under false positives, 7/8 vs 3/4) and one illustration (shared score), labelled as such | ✅ proved |
| `LeakWitness.lean` | a REAL leak for `audit_leak_bound`: BSC(ε) leak of the schedule, every hypothesis discharged, survival ≤ 1 − ε (attainment = 1 − ε by hand only) | ✅ proved |
| `tools/check_sc01_case.py` | proof / binding / evidence / applicability reported separately; exit 3 when a hypothesis is refuted; invokes the cache-receipt verifier; manifest assumptions carry provenance, testability, refuting lemma and experiment, and scoped witnesses | ✅ verdict HYPOTHESIS_REFUTED (exit 3) |
| `Gate.lean`, `GateClients.lean` | shared reference-monitor interface (F1/F3): `Spec.trace_safe`, `NoAgentEffects`, `withHalt` (absorbing shutdown for any gate; the spec lifts). Clients: AuditDispatch, AuditGate and EgressGate (existing gates; their step lemmas are reused) plus two new primitives: F4 content-addressed artefact gate (`deployed_is_reviewed` under collision resistance; `collision_breaks`) and F7 exact-payload approval (`approval_safe`: approved, unexpired, no replay; `replay_without_nonce`). After review: injectivity only on contents in the run; actor separation (`agent_cannot_approve`, `agent_cannot_review`); `replay_if_nonces_lost` (nonce durability is a premise) | ✅ proved (models only; no runtime for F4/F7) |
| adversarial review | Gemini 3.1 Pro + Opus 5.5 on all new Lean: no unsound proof; 3 + 13 model/definition/prose defects. [Disposition](reviews/adversarial-2026-10-08/disposition.md) | ✅ fixed or documented |
| `Lease.lean` | F5 as a gate client: `lease_safe` (per-lease spend over all forked workers ≤ budget, global cap, work only under unexpired issued leases), `work_count_le` (each unit costs ≥ 1, so units ≤ budget), `revoke_absorbing`, `revoked_worker_stays_stopped` (forks only to fresh workers), `agent_cannot_issue`, `fork_without_lease_accounting` (necessity) | ✅ proved (model; durability across restarts holds by definition) |
| `tools/ctrlcert.py` | researcher CLI: `channel`, `probe`, `audit`, `hazard`, `samples`, `diagnose`. Each number comes with its theorem, premises and refuting measurement; `--lean` emits a compiled instantiation. `diagnose` classifies LASR BigCodeBench as MARGIN and LinuxArena as PROTOCOL | ✅ tests pass; emitted Lean compiles |

## Lean track (2026-10-08)

See [LEAN-TRACK.md](LEAN-TRACK.md): side channels, usefulness gate, lifetime ledger, gateway core, SC-01 case
checker, coverage composition, multi-step attacks, audit budget.

## Current priorities after Astra/Opus xhigh consultation (2026-10-08)

See [review disposition](reviews/roadmap-consult-2026-10-08/synthesis.md). The
selected scenario is bounded exact-message recovery through finite machine
channels. Monitor-based bad-action safety is a separate optional second scenario.

| Order | Remaining milestone | Acceptance criterion |
|---|---|---|
| 1 | Complete the selected scenario contract and usefulness viability gate | Fix actual honest task, baseline/completion target, episode/lifetime horizon, receiver lineage and complete observation inventory; measure actual task success under the channel budget. |
| 2 — VM config passes; frozen usefulness gate fails | Enforce lifetime accounting and establish the VM observation boundary | [VM status](gateway/vm/STATUS.md): link-bound config check and 10 controls pass on H; the verified VM replay completes 0/64 lifetimes in both conditions at the unchanged 0.25-second deadline. Step 4 blocked, step 5 pending; case CONDITIONAL. Next: usable hardware virtualization/separate hosts or an owner-decided preregistered protocol amendment. Shared host/cache/timing and complete observations remain unresolved. |
| 3 | Targeted gateway/model correspondence | Validate schema/cardinality, blanking, delivery and lifetime charge behavior; consider a small proved executable core; retain explicit Python/OS correspondence assumptions. |
| 4 | One reproducible conditional safety/usefulness case | One command checks the theorem/config, runtime evidence, actual task-success measurement, exact revision bindings and unresolved obligations. |
| 5 | Demonstrate reusable interfaces with a second client | Common evidence/obligation format and small genuinely shared proof interfaces; optional monitor scenario must specify its protocol/content coverage before calibrating error rates. |

SC-03 outer-topology integration remains a bounded reachability track. Prioritize
it for the selected safety case only where it supports the actual observation
boundary; pinned peers and PID attribution do not establish confidentiality.
Sharper mathematics stays lower priority. Human specification/correspondence review
should happen once the revised contract is concrete, before expensive deployment work.

## 1. Completed

### Layer 1: collusion (untrusted monitoring with honeypots and a mediator)
| item | what it gives | status |
|---|---|---|
| UMHSF1 | testing core: hockey-stick/TV bounds, data processing, decoder floors, maximal leakage | ✅ verified |
| UMSURVF1 | honeypot-test survival = binomial CDF; first-moment bounds | ✅ verified |
| UMPROTF1 | main protocol bound for every colluding pair: (1 − r) + r·L·(n_s+1)/(n_h+1) | ✅ verified |
| UMSTRATF1 | stratified per-class honeypots: no class-count factor at fixed per-class budget | ✅ verified |
| UMNOGOF1 | rich decodable mediators lose against every iid honeypot law | ✅ verified |
| UMLOWERF1 | converse for nonadaptive test designs: budget ∝ number of decodable classes | ✅ verified |
| UMADAPTF1 | converse for ADAPTIVE testers, t(1 − tn/k); the nonadaptive formula provably fails for adaptive testers | ✅ verified (session 3) |
| UMADAPTF2 | sharp adaptive converse (t/k)·[(k−a)(1−t)^q + a(1−t)^(q+1)]; strictly beats UMADAPTF1, attained at the witness instance | ✅ verified (frozen cf874653d2fa; session 8) |
| UMUSEF1 | honest availability identities; mimicry constraint; Cantelli slack costs | ✅ verified |
| UMDEFERF1 | audit-then-defer: needs a uniform stopping hazard; no-go without one | ✅ verified |
| UMCERTF1 | certificate form: exact one-shot reduction, Lean-checkable grid certificates (0.154 → 0.07 certified), exactness results | ✅ verified (session 3) |
| TMCERTF1 | finite-horizon trusted-monitoring certificate checker with rectangular uncertainty, usefulness, rational checker and abstraction interface | ✅ verified (frozen 53a3bc12f43c; session 3) |
| TMCERTUSF1 | rational usefulness-certificate checker: sound lower bound on honest reward for every admissible history-dependent selector; accepted certificates are never vacuous | ✅ verified (frozen 3b0cda8ceba9; session 8) |
| TMLIPF1 | parameter-Lipschitz certificate transfer: one-step Bellman error, transfer, grid transfer over arbitrary target sets, policy-quantified risk corollary | ✅ verified (frozen 5c844eb0129e, override; session 8) |
| TMGACF1 | GAC safety/usefulness bridges and exact separation of constant-rate, coin-count and clocked Red | ✅ verified (frozen 89331ac41986; session 3) |
| CANONF1 | a verified canonicaliser (toy language) as a concrete trusted mediator | ✅ verified |

### Interface level (VCVio operational games)
| item | what it gives | status |
|---|---|---|
| `Spike` | TV bound for arbitrary `ProbComp` distinguishers | ✅ proved |
| `HoneypotBridgeProof` | the honeypot test as a crypto-style game is exactly binomial | ✅ proved |
| `RefinementProof` | trace-level protocol game = the core recursion; end-to-end bound | ✅ proved |
| `OutcomeProof` | five-outcome game; honest-completion bridge to UMUSEF1; Pareto identity | ✅ proved (session 3) |
| `SoftSlack` | soft-slack honeypot game: exact survival, seed factorisation, end-to-end bound (1−r)+r·L·n_s/(n_h+1) | ✅ proved (session 5) |
| `SoftHockey` | hockey-stick form of the soft-slack bound: (1−r)+r·(δ+e^η·n_s/(n_h+1)) | ✅ proved (session 5) |
| `StratifiedGame` | per-class binomial survival; end-to-end (1−r)+r·L·(s_c+1)/(m+1) under classwise domination and coverage | ✅ proved (session 6) |
| `DeferGame` | audit-then-defer game equals the exact `ENNReal` recursion, and under calibrated kernels equals the frozen UMDEFERF1 `catV` (`defer_bridge`) | ✅ proved (session 7; calibration is an equality on recall, halt and service rates) |
| `DeferMono` | **monotone defer bound** (`defer_mono`): recall ≥ r, halt hazard ≥ η and service catch ≥ a imply operational catastrophe ≤ ledger `catV`; with `defer_bridge` the bound is exact under calibration | ✅ proved (session 8) |
| `ComposeGame` | trusted + untrusted monitoring in one game; fresh trusted coins make the misses multiply: (1 − r) + r·τ·L·(n_s+1)/(n_h+1); tight at n_h = 0 | ✅ proved (session 8) |
| `ComposeAvg` | composition for any joint kernel (`composedJ_end`) and with the population-average trusted miss τ̄ = 1 − TPR (`composedPop_end`), so certified ROC bands plug in | ✅ proved (session 8) |
| `ComposeBlindSpot` | **negative result**: population-average trusted miss 1/1000, yet a content-adaptive Red reaches catastrophe w.p. 1; sampled ROC data cannot certify the per-submission τ | ✅ proved (session 8) |
| `CovertChannel` | covert-propagation bound: P(recover a uniform secret) ≤ |V|/|M| for every shared seed, adaptive encoder and decoder; schema form sⁿ/K; tight; design point 2^-16 | ✅ proved (session 8) |
| `GatewayModel` | Lean model of the gateway; any refusal blanks delivery; end-to-end bound (|S|+1)^slots/|M| for every adversarial raw trace | ✅ proved (session 8) |

### Empirical certification (preregistered; Lean-checked certificates)
| item | what it gives | status |
|---|---|---|
| LaStraj 2.0 (`PREREG-LASTRAJ.md`) | 30 honest / 17 attack; pipeline end to end | ✅ done; vacuous (≈1 at 100 tasks): too few attacks; Lean passes |
| LASR held-out test split, all 42 conditions (`PREREG-LASR-TEST.md`) | family-wise 95% over every condition | ✅ done; closed-source monitor 0.63–0.83 at 100 tasks, 0.05–0.22 per task; open-source ≈1; all 42 Lean checks pass |
| LinuxArena 217, cutoffs 7/3 (`PREREG-LINUXARENA.md`) | 250 honest / 150 attack, public task-set scores | ✅ done; per-task risk 0.115 (Opus attacker), 0.32 (Sol), but 92% of honest work deferred |
| LinuxArena 217, environment-split calibration (`PREREG-LINUXARENA-SPLIT.md`) | thresholds chosen on 2 environments, certified on 3 | ✅ done; FPR transfers (≤ 6.5%), per-task risk 0.82 (Opus): this monitor's exact safety–usefulness trade-off |
| Risk decomposition (`CERTIFICATE-DECOMPOSITION.md`, post hoc) | point estimate vs certified | ✅ done; weak monitors: the monitor is the limit; strong monitors at 100 tasks: statistical margin (needs ~1,000–3,000 attacks or predeclaring fewer cutoffs) |
| Statistical audit (`numerics/stat_audit.py`, post hoc) | duplication, epochs, clustering, matched populations | ✅ done; LASR clean (1 epoch, no duplicates); LinuxArena task ids and honest main-task scores are stripped in the public JSON (cannot audit repeats or report completion); matched-population split: TPR at ≥8 is 7/56 (band [0.04, 0.27]) vs 39/150 pooled, so detection does not transport across environments |
| Assurance manifests (`assurance/`, `tools/assurance.py`) | per-certificate theorem/data/preregistration hashes and assumption status; checker refuses to promote categories | ✅ done; 44 manifests, 0 deployment-grade |
| Held-out data search (`reviews/heldout-data-search-2026-10-07.md`) | public datasets, prior art (rocci; Gao 2026) | ✅ done |

### Layer 2: actions (first step)
| item | what it gives | status |
|---|---|---|
| SANDBOXF1, SANDBOX2F1 | mount-table model of a bubblewrap sandbox: the writable-root weakness and the corrected bind order | ✅ verified (model theorems; nothing deployed) |

## 2. In flight
| item | status |
|---|---|
| Lean checks of the 42 LASR certificates and 2 LinuxArena certificates | ✅ all pass (standard axioms) |
| GitHub export (private `jwcodes12/control-stack`) | ✅ egress slice/follow-up published on `egress-r10-controls` at `7efd2dc`; egress and existing CI passed |

## 3. Programme workstreams (2026-10-07 review; priority order revised above)
Goal: one end-to-end, independently checkable safety case, optimising for how much uncertainty each result removes.

| priority | work | definition of success | status |
|---|---|---|---|
| P0 | choose one concrete catastrophe and restricted deployment | explicit bad event, action space, threat model, horizon, acceptable usefulness | 🔄 `CATASTROPHE-SPEC.md` fixes exact recovery, machine receivers and finite channels (k = 32, P ≤ 2^-16, 16-bit lifetime budget); actual honest task, usefulness floor and horizon remain to be fixed |
| P0 | action gateway | every relevant tool action intercepted before execution; unauthorised actions fail closed | 🔄 v1: `gateway/` (schema channels, fail-closed, default-deny) running in a bubblewrap two-instance harness; side channels (files, network, stderr, exit code, duration) closed in tests; red-team within the Lean bound. Residual: shared kernel state (page cache timing) needs VM isolation |
| P0 | implementation correspondence | runtime traces refine the Lean transition model, or remaining assumptions stated | 🔄 `GatewayModel.lean` proves the end-to-end bound for the gateway model; Python matches the model on 300 adversarial traces (differential test); remaining assumptions in `gateway/CORRESPONDENCE.md` |
| P1 | empirical certificate validity | held-out, correctly timed measurements for matched populations; pre-action scores | 🔄 (preregistered runs done; transport and timing gaps found) |
| P1 | trusted/untrusted composition | Lean bound for the actual joint protocol incl. shared state and audit budget | 🔄 (`ComposeGame`, `ComposeAvg`, `ComposeBlindSpot`) |
| P1 | one reproducible safety case | a verifier reproduces the safety/usefulness pair and every unmet assumption | 🔄 (assurance manifests) |
| P1 | CI | fast tier plus proof/certificate checks for the safety case | 🔄 egress, fast, auditgate-db and narrow lean-covert jobs passed; complete safety-case replay and cited VCVio/certificate coverage remain |
| P2 | model coverage | multi-step attacks, stateful monitors, distribution shift, correlated failures; environment-state invariants | ⏳ |
| P3 | more mathematics | general balanced-schedule attainment (draft `ledger-drafts/UMADAPTF3-draft.lean`, shelved), sharper bounds | ⏸ demoted |
| — | human review | one AI-control researcher reads the specification and correspondence | 🔒 John |

## Session 8 status note (2026-10-08)
- Done this session: covert-channel bound, gateway prototype and Lean model; preregistered empirical certificates;
  LinuxArena replay (negative result for lexical host policy); auditgate v1.1 (database-level monitoring-integrity
  gate, Lean invariants, PostgreSQL outcome matrix in CI) with a documented no-go for auto_workflow as deployed.
- Historical session-8 pause: SC-03 subsequently completed its local slice and remote CI; outer attribution remains open. SC-16 (provenance gate) remains paused. Work on them was interrupted
  repeatedly in this session; requirements for SC-03 are in reviews/dialogue/chatgpt-08.md and chatgpt-10.md.
- Dialogue with the external reviewer: latest rounds are chatgpt-10.md (awaiting a Claude round 11).

## 4. Open assumptions (what the stack does NOT give)
Every guarantee is conditional on these. None is discharged by anything here:
- the mediator's domination constant L (or δ), and honeypot constructibility and coverage (A9);
- worst-case audit recall r (A6);
- the scaffold properties: fresh stateless monitor calls, complete views, test before deployment, absorbing shutdown
  (A1–A4, A11);
- for TMCERT, row coverage of the concrete deployment (Abs). An average ROC estimate does not discharge it.

## 5. Needs John 🔒
- **Scaffold enforcement**: turn A1–A4/A11 into runtime checks or verified code (stateless calls, no clock exposure,
  test before deploy, absorbing shutdown). It touches deployment.
- **Sandbox fix**: deploying the corrected bind order (SANDBOX2F1) in the research harness.
- **Human expert review**: one control researcher reading STACK.md. All review so far has been model-based.
- **Visibility**: the GitHub repo is private; making it public is a separate decision.

## Maintenance
Update this file whenever a row changes status: verified, frozen, started, or dropped. Also update the matching row in
STACK.md, and note the change in HISTORY.md when a new snapshot is exported.

## SC-01 repair milestone — 2026-10-08

Implemented the contract/usefulness milestone and durable SQLite lifetime charging.
See `gateway/scenario/README.md`, the two preregistrations, source-bound receipts
and `ControlStack/ScenarioARepair.lean`. Contract preregistration: `1001024`.
Baseline and mediated repair each passed 320/320 episodes and 64/64 lifetimes;
simultaneous completion lower bound 93.382% exceeds the 90% floor. Ten ledger
controls, five scenario/oracle/evidence-mutation tests, ten gateway tests, selected
harness probes, three new standard-axiom Lean checks and full
`lake build ControlStack` (3,691 jobs) passed. Both final receipt verifiers passed.

The targeted shared-cache experiment decoded one secret bit in 64/64 trials with
a constant NULL gateway view. This falsifies the sole-transcript premise in the
current harness. It does not demonstrate full-secret recovery; the finite-view
Lean bound remains model-only and the case stays CONDITIONAL. Initial results
and corresponding changed source snapshots are retained, not pooled.

Next blocker: stronger isolation or a justified bound covering all receiver
observations, followed by repeat probes and gateway/model correspondence. Valid
host snapshot rollback, statistical runtime independence and workload transport
remain assumptions. Auditgate untouched. Private tracker: GitHub issue #2.
