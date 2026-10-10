# Control-stack: From Conditional Lean Models to a Portable Deployment Verifier

**Repository:** [jwcodes12/control-stack](https://github.com/jwcodes12/control-stack)  
**Assessment date:** 9 October 2026, 11:18 p.m. US Eastern (10 October UTC)  
**Verified baseline:** `main` at [`ed35a41df99021bc90f46e7d93b3bda6fe2ad5a5`](https://github.com/jwcodes12/control-stack/commit/ed35a41df99021bc90f46e7d93b3bda6fe2ad5a5), following merged PR #42  
**Relevant open work:** [PR #43](https://github.com/jwcodes12/control-stack/pull/43) (portable wire contract; head `ad28a68e...`) and [PR #41](https://github.com/jwcodes12/control-stack/pull/41) (overlapping runtime/F6/F8 work; mergeability reported false at inspection)  
**Method:** Read-only review of the live GitHub repository, selected code and documentation, PR metadata, the tree, and visible CI runs, plus official external project documentation. **This is an architectural assessment, not an independent source-level security audit, a clean local build, or a live deployment test.**

---

## Executive decision

**Keep the existing repository and preserve its proofs/evidence. Refactor around a new, explicit, reusable security intermediate representation (IR), rather than beginning a new verification repository or writing scenario-by-scenario bespoke proofs.** The central product should take a **real deployment snapshot**, extract a conservative model of its capabilities, instantiate the existing Lean theorem library, explain any unresolved assumptions, and optionally synthesize a restricted deployment that can then be tested and assessed.

The right first product is a **Linux/Docker Compose scoped deployment verifier for agent + MCP-style tool stacks**. It should be able to produce one complete report and enforce a small set of consequential effects, with a documented scope and a reproducible end-to-end example. Kubernetes extraction and ControlArena integration should follow; WASI and non-Linux native backends are later extensions, not prerequisites for a usable initial release.

**Current strength:** control-stack is already a rich formal methods research repository, not an empty prototype. The generated `OVERVIEW.md` reports **28/28 conditional scenario models**, **157 distinct manifest-cited theorems**, **23 scenarios with preregistered runtime evidence**, **seven scenario refinement results** and **no deployment-assured scenarios**. There is already a reference SQLite broker, a narrow real Linux-confined effect path, differentiated reviewer/approver identities, finite differential checks, F6 statistical machinery and F8 shared-budget/delegation verification. [Repository overview](https://github.com/jwcodes12/control-stack/blob/main/OVERVIEW.md)

**Current weakness:** these components are not yet joined into an automated, general-purpose verification pipeline. No canonical deployment-security IR, supported deployment extractor, conservative unknown-capability analysis, universal adapter contract, soundness evidence for extraction or operational product release criteria were identified in the reviewed `main` tree. The Linux launcher deliberately does **not** prove complete mediation of arbitrary OS effects; the cross-language work in PR #43 demonstrates RPC interoperability, **not** cross-platform confinement.

**Near-term goal:** a reproducible **scoped assurance report**, not a certificate that an arbitrary computer is safe. A genuinely strong claim requires a policy theorem *and* a justified correspondence between the deployment, abstract capabilities and runtime enforcement. Unknown paths must fail closed or remain plainly marked *unassured*.

### Decision table

| Choice | Recommendation | Reason |
|---|---|---|
| Proof strategy | **Reusable parametric Lean theorems** + per-deployment generated instances/certificates | Avoid bespoke proofs for every compute blob; proofs change when the *security protocol*, not the application language, changes. |
| Repo strategy | **Evolve in place**, organize under `security_ir/`, `extractors/`, `verifier/`, `adapters/`, `integrations/` | The existing theorem registry, evidence, scenario models and CI are valuable; wholesale migration would create unnecessary fidelity and provenance risk. |
| First extraction target | **Docker Compose plus container image/runtime inspection on Linux** | A constrained, inspectable unit that covers tools, credentials, networking and processes without immediately taking on all Kubernetes semantics. |
| First enforcement target | **Explicit broker-owned file and outbound HTTP effects in a disposable, isolated workload** | Extend the real effect path narrowly and honestly, rather than promise interception of arbitrary syscalls. |
| First research integration | **ControlArena / Inspect-compatible trace export and replay** | Distinguishes monitor misses from policy bypasses, coverage gaps and adapter failures. |
| Release designation | **Experimental research tool / scoped Linux beta** | Neither existing nor proposed initial work justifies general deployment safety assurance. |

## 1. Current repository: what is actually there

### 1.1 Formal proof and assurance assets

- `ControlStack/Core`, `ControlStack/Families/F1`–`F8`, `ControlStack/Scenarios`, `ledger/` and `proofs/` form a large, reusable collection of idealized safety models, bounds, premises, witnesses and proofs.
- `ControlStack/Core/TrustRoot.lean`, `THEOREM-REGISTRY.*`, `ASSURANCE-LEDGER.md`, `OVERVIEW.md`, `tools/portfolio_ledger.py` and generators already provide a source-indexed assurance inventory rather than just isolated theorem files.
- The repository's own ledger identifies **29 normalized assumptions**. The most widely shared are `credential_separation` (19 scenarios), `honest_usefulness` (18), `exclusive_effect_path` (11), and `model_runtime_correspondence` (9). These are the ideal starting points for generalized proof obligations. [Assurance ledger](https://github.com/jwcodes12/control-stack/blob/main/ASSURANCE-LEDGER.md)
- Seven scenario-specific refinements are recorded for **SC-07, SC-16, SC-18, SC-25, SC-26, SC-27 and SC-28**. The backlog explicitly names **11 other runtime-tested scenarios** awaiting their own runtime-to-model refinement; these are still not proofs of arbitrary Python/OS behavior. [Refinement gaps](https://github.com/jwcodes12/control-stack/blob/main/docs/REFINEMENT-GAPS-2026-10-09.md)
- There is a good existing culture of source hashes, preregistered experiments, negative controls, theorem-statement fidelity checks, standard-axiom checks and explicit qualification of assumptions.

**Assessment:** Mature enough to supply much of the **theorem catalog and assurance vocabulary**. Not yet a formal model of independently discovered real deployments.

### 1.2 Existing runtime and testing

- `trusted_stack/server.py` and `controller.py` provide a Python/SQLite trusted reference broker, with Linux Unix-domain-socket `SO_PEERCRED` caller identity and separate agent/reviewer/approver/admin roles.
- Admission includes digest-bound artifacts, review and approval, one-use nonces, leases, shared budgets, revocation and sticky HALT; the modeled effect is recorded transactionally. `trusted_stack/outbox_receiver.py` supports a narrow trusted local filesystem effect and explicitly addresses publication/receipt crash windows.
- Merged PR #42 adds `trusted_stack/agent_confinement.py`: a **single-process** non-root Linux launcher using Landlock, libseccomp, `no_new_privs`, fd closing and denial of enumerated syscalls. `tools/test_confined_effect_broker.py` exercises a real confined broker-mediated local effect with OS identities. The project's own documentation warns that this is a deny-list profile, not an exhaustive Linux syscall security proof and not whole-host containment. [Linux confinement scope](https://github.com/jwcodes12/control-stack/blob/main/docs/AGENT-LINUX-CONFINEMENT.md)
- F8 adds a two-agent, shared-budget Lean model and runtime concurrency/adversarial tests; F6 adds an anytime-valid historical conditional-average calibration procedure and an **exploratory**, post-hoc 171-monitor-pair analysis on LaStraj data. These are genuine additions but do not independently establish future adaptive monitor recall. [F8 scope](https://github.com/jwcodes12/control-stack/blob/main/docs/F8-DELEGATED-FLEET.md); [F6 scope](https://github.com/jwcodes12/control-stack/blob/main/docs/F6-ANYTIME-MONITOR.md)
- There are approximately **40 GitHub Actions workflow files** on `main`, covering varied scenario, fidelity, model, and runtime checks. The latest inspected PR #43 head had visible successful fast, egress, integrity, scenario and polyglot runs; **that does not establish that every required check, independent review or branch-protection requirement is satisfied**.
- `tools/cstack.py` is already a practical internal CLI for status, checks, ledgers, scenario generation, evidence and stack mapping. `tools/ctrlcert.py` instantiates some general risk/bound calculations. These should be extended, not replaced.

**Assessment:** Credible, narrowly scoped reference enforcement and research tooling. Not a host-independent effect enforcement product, not an audited general runtime, and not an arbitrary deployment scanner.

### 1.3 Work in flight and branch hygiene

**PR #43** introduces `interop/PORTABLE-EFFECT-CONTRACT.md`, a zero-dependency Node client, a Linux Node/Python broker conformance test, and workflow coverage. Its documentation correctly distinguishes request wire format, identity binding, admission state, and host-specific effect execution. **Recommended: merge only after exact-head required checks and review, then treat it as the v0 interoperability seed—not the completed IR.** [PR #43](https://github.com/jwcodes12/control-stack/pull/43)

**PR #41** contains overlapping outbox and F6/F8 candidate work on an older base. At inspection it was open and reported nonmergeable. **Recommended: reconcile its unique changes against already merged #40/#42; cherry-pick only independently useful, current-head-clean material or close it as superseded.** Do not merge stale overlapping changes wholesale. [PR #41](https://github.com/jwcodes12/control-stack/pull/41)

Some root docs retain dated, historical summaries (for example, `ROADMAP.md`'s opening text), whereas the generated overview is newer. Define a single release-status source and mark historical handoffs and PR-specific `COMPLETED.md` content accordingly. In particular, **do not upgrade all 28 scenario statuses merely because the new product's first narrow use case passes**.

## 2. Target product and explicit non-goals

### 2.1 Proposed user experience

Given a project containing a Docker Compose deployment (later Kubernetes manifests), the user should be able to run something equivalent to:

```bash
cstack scan ./deployment --format json --output out/model.json
cstack verify out/model.json --policy policies/agent.yaml --output out/assurance.json
cstack report out/assurance.json --format markdown --output out/report.md
cstack plan out/model.json --policy policies/agent.yaml --output out/remediation.yaml
cstack test ./deployment --plan out/remediation.yaml --output out/runtime-evidence.json
```

**These are proposed CLI contracts, not commands implemented today.** The CLI must show which inputs were read, which collectors were unavailable, what was actually proven, and which environmental assumptions remain open. Remediation should be reviewable; it must never silently rewrite production infrastructure.

The product should answer four concrete questions:

1. **Declared intent:** what do prompts, MCP/tool definitions, role/config files and application policy *claim* is allowed?
2. **Effective authority:** what can relevant processes actually reach through identities, file mounts, inherited descriptors, service tokens, routes, tool servers and delegation?
3. **Formal outcome:** for each reusable security theorem, which premises are established by machine-checkable facts, which are measured or tested, and which are unknown?
4. **Remediation and runtime evidence:** which deployment changes would close a missing effect path, and what tests prove the promised restriction was actually installed in a scoped environment?

### 2.2 Canonical IR: the missing architectural layer

Represent the deployment with a **versioned, typed, conservative** graph plus event semantics. At minimum:

- **Principals**: workload identities, OS users, service accounts, tool servers, reviewers, approvers, parent/child agents.
- **Resources**: local files/mounts, services, network destinations, credentials, code repositories, audit logs, external APIs.
- **Capabilities**: read/write, spawn, send, delegate, approve, deploy, access secrets, request a broker-mediated effect.
- **Edges and transitions**: process starts, socket connections, token grants, calls, approval issuance, budget consumption, publication, revocation, HALT and in-flight completion.
- **Observations**: returned data, errors, files, logs, visible timings where specified; *not* an implicit claim to include all physical/side channels.
- **Controls and trust roots**: gate, identity binding, policy integrity, credential custody, mediation boundary, external sink and durable receipt semantics.
- **Evidence/provenance**: source paths and hashes, collector version, runtime image digest, platform and API versions, inspection time, signed attestation where present.
- **Unknowns**: uninspected service accounts, dynamic tool loading, unsupported syscall behavior, opaque sidecars, foreign credentials or routes. **Unknown is a first-class state; it never means denied.**

Each extractor emits an assertion with provenance and a confidence/assurance **kind**, not a misleading confidence percentage: `DECLARED`, `STATIC_INFERRED`, `RUNTIME_OBSERVED`, `ENFORCED_TESTED`, `EXTERNALLY_ATTESTED`, `FORMALLY_DERIVED`, or `UNKNOWN`. Observed-but-not-seen is never equivalent to unreachable.

Avoid turning arbitrary Python source, prompts, or networking logs into universal correctness assertions. Prefer conservative overapproximation of accessible effects; if the tool cannot represent an effect class, exclude it explicitly from the claim and present a failed/unknown global assurance result.

### 2.3 Reusable theorem interface

The majority of deployment-specific work should be **instantiation and evidence collection**, not new Lean theorem invention. A central Lean theorem could have the form:

```lean
-- Schematic interface, not compiled code.
theorem admitted_effects_safe (d : Deployment)
    (hCapture : CompleteMediation d)
    (hGateway : GatewayImplementsPolicy d)
    (hIdentity : AuthenticatedCallers d)
    (hAtomic : AtomicBudgetAndNonce d) :
    EveryProtectedEffectAuthorized d := by
  ...
```

The verifier should produce an **obligation bundle** for a particular deployment: which assumptions were solved statically, which need a trusted runtime/OS adapter, which are merely tested, and which cannot presently be discharged. It may generate Lean certificate instances where the semantics are finite/decidable or a formally justified decision procedure exists. SMT and graph searches can provide counterexample candidates; **a solver result is not automatically a Lean-checked proof** unless accompanied by an independently checked certificate or trusted, explicit axiom.

Non-vacuity is mandatory: a trivial reject-all deployment might satisfy safety, but fail usefulness. Every major theorem family should have a positive allowed-action witness, a check-disabled counterexample, and an explicit attacker/observation/time scope.

### 2.4 Assurance semantics

The key claim is a *conditional trace refinement*:

```text
abstract(Traces(actual deployed runtime)) subset Traces(extracted/validated model)
AND model traces satisfy the stated policy
THEREFORE actual scoped effects satisfy the policy.
```

This is a sound basis for portable theorems, **not an assertion that the repository already proves the first inclusion**. Proving the first inclusion for an arbitrary native application and OS is usually far harder than proving the abstract policy property. A practical initial release must bound it to a carefully defined workload, closed set of effect APIs and audited launch path; everything else remains outside assurance.

**Important conceptual distinction:** static extraction can show candidate effect routes; runtime tracing demonstrates some observed routes; a trusted confinement mechanism may enforce that alternate routes cannot be used. None of these three should be substituted for another.

## 3. Current vs ideal: precise gap analysis

| Dimension | Existing `main` (9 Oct 2026 ET) | Stable v1 target | Gap severity |
|---|---|---|---|
| Lean theorem library | Many conditional scenarios, families, witnesses, ledger | Parametric deployment-facing interfaces with reusability tests | **Medium**: significant assets exist, need API rationalization |
| System model | Hand-built scenario transitions and component mapping | Canonical, versioned, typed deployment IR | **Critical** |
| Automatic extraction | Scenario skeletons and manual component maps | Docker/Compose collector; static + optional live inspection | **Critical** |
| Soundness of extraction | Not established for arbitrary deployments | Conservative unsupported/unknown semantics, formally specified extractor contract, tested adapters | **Critical** |
| Effective permissions | Selected broker identities and local sandbox tests | Principal/resource/capability graph including inherited and delegated paths | **Critical** |
| Consequential effects | SQLite releases and narrow local-file receiver; scoped Linux launcher | All effects **in a declared finite set** have reviewed sink ownership and enforced mediation | **Critical** |
| Languages | Python broker; Node/Python client PR pending | Versioned RPC contract with multiple conformance clients | **Medium** |
| Operating systems | Linux-specific confinement and receiver | OS-neutral core; explicitly scoped Linux backend; other backends independent | **High** for portability; **not beta blocker** |
| Model/runtime link | Scenario refinements + bounded differentials; residual assumptions | Transition correspondence for supported adapter scope with independent validation | **Critical** |
| Multi-agent | F8 shared budget/delegation models + tests | Live parent/child identity and budgets, revocation and crash semantics in one reference workload | **High** |
| Monitoring (F6) | Conditional theorems, exploratory LaStraj, historical anytime estimator | Held-out predeclared monitor evidence linked to covered effect paths | **High** for probabilistic claims; **not static scanner blocker** |
| Review/certification | AI reviews, generated packet, unresolved independent human review | Independent statement/assumption review and signed scope-bound evidence | **Critical** for strong assurance labels |
| User experience | Researcher CLI, many internal scripts | `scan`, `verify`, `report`, `plan`, `test`, deterministic JSON outputs | **High** |
| CI and release | Many independent workflows; substantial evidence | One required end-to-end release matrix, reproducible installs, frozen fixtures, security gates | **High** |
| Research integration | Dataset/replay artifacts in repo | ControlArena plugin plus coverage/bypass attribution and empirical reports | **High** for research impact |

## 4. Build the smallest complete vertical slice first

A stable, valuable first product does **not** need AWS/GCP/Azure, Kubernetes, Windows, macOS and WASI on day one. Its smallest believable promise is:

> **For a Linux deployment started through the supported runner, all writes to one designated protected filesystem sink and all egress to one designated protected HTTP sink are broker-mediated, while an explicitly enumerated set of other effects is denied; the report proves the admission invariants in Lean and tests the real confinement boundary under negative controls. Any unmodeled effect route prevents a complete-mediation assertion.**

The initial `scan` input should be a pinned Docker Compose file, image digests, service definitions, env var names (never secret values), mount maps, user IDs, network bindings, known MCP/tool declarations and selected runtime inspection metadata. Build a **read-only first pass** before adding enforcement.

The first demo application should have two agents, one trusted tool server, one protected external destination, one untrusted service with a deliberately exposed alternate egress path, shared budgets and review. The report should find the bypass, refuse certification, propose a restricted configuration, rerun a real attack and honest task, and issue a **scope-bound conditional verdict**.

**Adversarial negative controls:** direct curl/socket egress; inherited fd; Unix-socket confused deputy; unapproved write; symlink race; token theft simulation; nonce replay; child spawn; shared-budget double spend; HALT during in-flight publication; crash after external commit before receipt; alternate namespace/host-network route; policy/config tampering. Tests must distinguish **BLOCKED**, **SUCCEEDED**, **UNOBSERVED**, and **UNSUPPORTED**.

A stable beta should **not** advertise that it blocks all Linux effects. If `ioctl`, DMA, timing channels, external same-UID helpers or any other class is unmodeled, put the limitation in the threat model and machine-readable report.

## 5. Proposed repository structure (in-place evolution)

```text
ControlStack/
  Core/                 # Retain and refactor shared assurance lemmas
  Families/F1..F8/      # Existing theory
  Deployment/           # NEW: typed principals, resources, capabilities, effect traces
  Contracts/            # NEW: admission, identity, delegation, HALT, refinement contracts
  Instances/            # NEW: generated, version-pinned instances of reusable theorems
security_ir/             # NEW: versioned schema + validation + golden fixtures
extractors/
  compose/              # NEW: declared configuration and image/runtime collector
  linux/                # NEW: OS identity, mounts, fd/egress evidence collector
  kubernetes/           # LATER: RBAC/NetworkPolicy/admission/workload identity
verifier/                # NEW: conservative graph analysis and proof obligations
adapters/
  linux/                # NEW: scoped confinement + trusted filesystem/HTTP sinks
  wasi/                 # LATER: capability-host adapter
  windows/              # LATER: independently evaluated confinement
  macos/                # LATER: independently evaluated confinement
interop/                 # PR #43 request contract/Node client, later clients and tests
integrations/
  controlarena/         # NEW: Inspect/ControlArena compatible replay and reporting
trusted_stack/           # EXISTING broker; avoid destabilizing historic tests
scenarios/               # EXISTING immutable/controlled evidence organization
ledger/, proofs/         # EXISTING frozen proof history
examples/
  compose-two-agent/    # NEW: sample deployment, genuine bypass and remediated variant
reports/                 # NEW: reproducible report schemas, NOT frozen results
.github/workflows/      # Keep historical checks; add one release acceptance gate
```

Use the existing `cstack.py` front door. Maintain backwards-compatible historical paths/imports and generated registries. Avoid a second competing status database. Existing frozen preregistrations, experiment receipts, evidence hashes and **`ControlStack/EgressGate.lean` must remain untouched**; create new versioned work alongside them.

## 6. Implementation roadmap and exit gates

Estimates below are **rough engineering effort** (one experienced contributor familiar with Lean, Python, Linux security and CI), not elapsed-time promises; complicated kernel/platform work and external review can expand them substantially. Parallel contributors can shorten calendar time, not the need for independent validation.

### Phase 0 — Freeze baseline and reconcile branch work (3–5 engineer-days)

**Deliverables:** pin `main` baseline and evidence manifest; review and integrate/supersede PR #43; inventory unique PR #41 changes; document CI/test/Lean matrix; designate generated sources, frozen sources and current status authority; add a one-command smoke/reproducibility script.

**Exit:** clean `main`, full current required CI green at exact commit, no changed protected evidence/`EgressGate.lean`, no ambiguous open duplicate PR, and an accurate `CURRENT-STATE.md`. **Do not block this phase on external human assurance review.**

### Phase 1 — Canonical IR and abstract proof contracts (2–3 engineer-weeks)

**Deliverables:** schema v0.1; serializable principal/resource/effect graphs; three-valued reachability (`allowed`, `denied`, `unknown`); unknown-source tracking; typed event machine; source-provenance records; reusable Lean theorem interfaces (`complete_mediation`, `one_use`, `shared_budget`, `delegation_attenuation`, `halt_no_new_commit`, `approval_exact_payload`). Map existing F1–F8 theorem inputs to the IR and record noncovered semantics. Do not rewrite existing proven mathematics unnecessarily.

**Exit:** synthetic examples instantiate at least four theorem families; independent schema validator rejects contradictory/missing data; planted unknown route produces *unassured*, not *safe*; kernel builds, positive witnesses, falsifying mutations and deterministic generated certificates pass.

### Phase 2 — Compose/Linux conservative extractor (2–4 engineer-weeks)

**Deliverables:** parse pinned Compose definitions and image metadata; optionally inspect a live disposable container host using a read-only collector; map users, mounts, namespaces, networks, host privileges, process launch, env secret references, service tokens, tool declarations and supported delegation edges into IR. Record missing evidence. Integrate network-reachability or policy tools where semantics are compatible rather than asserting their output proves a whole deployment.

**Exit:** a golden corpus of at least 12 adversarial/benign fixtures with known routes; seeded privileged mount/host-network/direct-egress/alternate credential paths must not be missed; unsupported platform features must fail with actionable `unknown` findings; extraction must be repeatable from identical pinned inputs.

### Phase 3 — Enforcement synthesis and actual scoped effects (3–5 engineer-weeks)

**Deliverables:** explicit broker-exclusive filesystem sink and outbound HTTP proxy in a disposable container/VM; bounded approved-effect grammar; authenticated principal identity; closed, scoped guest launch path; durable idempotency/receipt protocol; explicit crash, retry and HALT fencing semantics; static remediation diff and policy simulation. Separate broker admission from external delivery, and separately model all in-flight effect states.

**Exit:** all P0 negative controls fail to bypass **the declared sink scope**, honest end-to-end tasks complete, failures default deny, crash injection reconciles admitted vs delivered vs unknown-commit effects, and every test produces independent sink-side evidence. No assertion of universal native syscall confinement.

### Phase 4 — Assurance engine and stable CLI (2–3 engineer-weeks)

**Deliverables:** `scan/verify/report/plan/test` CLI; JSON schema for proof obligations, claims, evidence, confidence assumptions and unsupported scopes; human-readable Markdown/HTML reporting; stable exit codes; hash-pinned artifact manifest; explicit `PROVEN_IN_MODEL`, `TESTED_BOUNDARY`, `CONDITIONAL`, `REFUTED`, `UNASSESSED` statuses; deterministic CI result and clear remediation suggestions.

**Exit:** fresh Linux workstation can follow documentation from checkout to bounded assurance report; all outputs have evidence provenance; no success classification derives merely from a green harness; report fixtures and the security-critical CLI are versioned and regression-tested.

### Phase 5 — ControlArena evaluation integration and independent validation (3–6 engineer-weeks, some external dependencies)

**Deliverables:** exporter for Inspect/ControlArena-style episodes and tool calls; comparison of baseline vs mediated protocol on representative honest and adversarial tasks; attribution of attack outcome (monitor miss vs structural bypass vs permitted-policy abuse vs evidence gap); predeclared held-out monitoring protocol where possible; performance, operational failure and false-positive metrics; external reviewer packet.

**Exit:** a pinned, reproducible end-to-end evaluation with a clean separation between structural enforcement and empirical monitor effectiveness; independent review checks theorem statement fidelity and operational assumptions; any discrepancies are recorded as explicit failures, not quietly excluded. **No operational F6 per-history guarantee without externally justified sampling/coverage assumptions.**

### Phase 6 — Expansion (post-beta, not a prerequisite)

Kubernetes extractor with explicit CNI/`hostNetwork` and admission-controller semantics; workload identity/cloud IAM plugins; WASI component capability-host proof boundary; Windows and macOS backends with **their own** trusted-code and kernel assumptions; remote attestation/rollback-resistant evidence; deeper cross-agent confidentiality and noninterference analysis; deployment drift revalidation.

**Indicative effort:** Phases 0–4 total **roughly 9–16 engineer-weeks**, plus Phase 5 **3–6 engineer-weeks**, assuming suitable Linux testing infrastructure and bounded integration. This is a planning range, not a verified estimate. A broad, multi-OS, independently security-reviewed product is a substantially larger research/engineering project.

## 7. Stable-and-usable acceptance checklist

**Do not release even an experimental beta until all P0 criteria are satisfied:**

| Gate | Required evidence |
|---|---|
| Truthfulness of scope | Report never says *safe/fully mediated* if any protected effect path is unknown, bypassable or outside stated boundary. |
| Model provenance | Every graph node/edge says where it came from; input, policy and image digests pinned. |
| Reusable Lean | Instantiated theorem checked under pinned toolchain; axiom reports and statement-fidelity review recorded; no banned holes/unsafe axiom introduction. |
| Confinement | Real Linux kernel / network tests on a supported host; skips/unsupported environments never count as passes. |
| Independent observation | Sink-side effect log/receiver state not solely produced by the gate under test. |
| Denial and usability | All predeclared seeded bypasses blocked or result in `UNASSESSED`; a representative allowed end-to-end task succeeds. |
| Concurrency & durability | Shared budget, delegation, replay, crash, lost acknowledgement and HALT tested against actual broker+sink. |
| CI/reproducibility | Required exact-head CI green; reproducible one-command fixture; no modifying frozen evidence in CI. |
| Developer experience | Quickstart, supported platforms/versions, examples, deterministic CLI, meaningful error messages and machine output. |
| Documentation | Clear claim ladder: proved abstractly vs live-tested vs externally assumed vs empirically measured. |
| Security review | Threat model and code review for the trusted path; clearly identify open independent review if it has not occurred. |

**Release maturity ladder:**

- **R0 / theory:** reusable Lean theorem with explicit assumptions. The repository largely has this.
- **R1 / static analyzer:** conservative deployment extraction and proof-obligation report; *no* deployed enforcement claim.
- **R2 / scoped beta:** restricted Linux workload; real sink ownership and bypass tests; conditioned/limited proof-backed report.
- **R3 / reviewed scoped assurance:** independently reviewed semantics, enforcement, evidence custody and explicit deployment version within one host/security boundary.
- **R4 / portable extension:** one OS-neutral model with **separately validated** enforcement adapters; never infer Windows/macOS verification from Linux CI.

The first worthwhile shipping milestone is **R1**, followed by a credible **R2**. Do not require R3 or R4 to demonstrate research usefulness, but do not imply their guarantees in an R1/R2 report.

## 8. Redwood/AISI ControlArena and DeepMind: how to show actual value

The closest research fit is a **ControlArena protocol wrapper + capability/assurance sidecar**. ControlArena (UK AISI with Redwood Research) provides controlled environments, honest and attack trajectories and protocol components. Control-stack could certify parts of the *plumbing* independently of a model's willingness to comply. [ControlArena documentation](https://control-arena.aisi.org.uk/)

**Proposed evaluation:** use one sandboxed coding/tool environment and a pinned set of attacks, with four arms: (A) unmonitored baseline, (B) monitor-only, (C) broker+confinement only, (D) monitor+broker+confinement. In all arms, measure **honest-task usefulness**, attempted adverse effects, effects actually committed at an independent sink, monitor alert behavior, latency/overhead and unknown or unobserved channels. To test improvements credibly, use preregistered scenarios/thresholds, fresh held-out attacks and matched attack budgets; avoid tuning on the evaluation sample.

An attack succeeding in B but not D may be evidence of **enforcement rather than better monitor intelligence**. Conversely, if a task is authorized by a mistaken policy, even a correctly implemented broker may allow harm; classify it as a policy/semantic-review failure. If a detector misses an attacker-controlled path that the runtime cannot mediate, call it a structural coverage failure, not merely a recall problem.

The link to Google DeepMind's 2026 AI Control Roadmap is especially direct: GDM evaluates **coverage**, **recall** and **time-to-response**, and calls for synchronous prevention for sufficiently consequential effects. Control-stack could contribute sound, *scoped* mediation evidence for **coverage**, empirical procedures for **recall**, and temporal/refinement checks for **pre-effect response**. It cannot formally prove a real monitor's future recall without justified distributional and sampling assumptions. [Google DeepMind roadmap announcement](https://deepmind.google/blog/securing-the-future-of-ai-agents/)

**Suggested research result to pursue:** “A generic Lean control theorem was instantiated automatically for an unseen Compose agent deployment; the extractor identified a real bypass; the generated remediation removed it in the declared effect scope; the positive workload remained useful; and independent sink observations plus kernel-checked proof obligations support an explicitly conditional assurance claim.” That is more externally legible than a larger tally of scenario models alone.

## 9. External software to reuse—without confusing evidence types

| Candidate | Reuse | Limitation / trust boundary |
|---|---|---|
| [Cedar specification in Lean](https://github.com/cedar-policy/cedar-spec) | Verified authorization language semantics and differential-testing ideas | Does not automatically prove a Docker/Kubernetes deployment implements a Cedar policy. |
| [Batfish](https://github.com/batfish/batfish) | Vendor-independent network models, reachability and policy counterexamples | Best for supported network device configurations; not a blanket container/OS capability extractor. |
| [AWS IAM Access Analyzer](https://docs.aws.amazon.com/IAM/latest/UserGuide/access-analyzer-concepts.html) | Provider-native IAM reasoning and policy findings | AWS-specific; identified resource scope and analyzer limits matter. Use findings as attributed inputs. |
| [OPA/Conftest](https://github.com/open-policy-agent/conftest) | Structured config parsing, linting and admission/preflight rules | Policy compliance test, not proof that an adversary cannot find another effect route. |
| [ControlArena](https://control-arena.aisi.org.uk/) / Inspect | Adversarial task/agent traces, honest usefulness, protocol comparisons | A benchmark score does not establish host mediation or future adversarial recall. |
| [WASI/component model](https://wasi.dev/) | Portable capability-host route for suitably compiled tools | WASI 0.3 is current, but language/toolchain coverage varies; backend/capability host still needs its own assurance. |

Integrate reusable tools **behind typed provenance-bearing collectors**, not by treating their judgments as axioms. A Batfish reachability result, IAM finding and OPA rule can disagree because their scopes differ; the IR should preserve that distinction.

## 10. Main engineering risks and mitigations

1. **Unsound extraction masquerading as proof.** Require conservative abstractions, source spans, unknown edges, seeded bypass fixtures and independent negative controls. No collector may infer “denied” from absence of a log entry.
2. **Adapter explosion.** Finish one complete Linux backend before Kubernetes/non-Linux; keep protocol and adapter contracts separate. Do not require runtime language rewrites when broker RPC suffices.
3. **Trusted computing base creep.** Explicitly enumerate launcher, broker, kernel primitives, sink credentials, database/clock, parser, policy compiler and collector. Minimize privileged code and independently test it.
4. **Lean proof validity vs claim fidelity.** Review theorem propositions, hidden premises, observation/time scope, vacuity and runtime simulation. Kernel acceptance alone is not the required assurance.
5. **External effect transactionality.** SQLite approval and external HTTP/filesystem commit cannot generally be one atomic transaction. Model uncertain completion; require sink idempotency/fencing where available, never call lost acknowledgements “no effect.”
6. **Statistical overclaim (F6).** Historical conditional-average bounds do not imply worst-case unseen attacker-history recall. Require appropriate fresh held-out designs and report uncovered histories.
7. **Evidence integrity and stale outputs.** Pin configs/images/monitor thresholds/theorem toolchains. Reverification must be triggered on significant drift; generated docs cannot silently present historical status as current.
8. **Usability failure.** A deny-all tool is trivially safe but not useful. Honest-task completions, latency and controlled privilege-request workflow belong to acceptance tests.

## 11. Prioritized initial work queue

| Priority | Work package | Depends on | Definition of done |
|---|---|---|---|
| **P0.1** | Reconcile #41/#43, pin baseline and clean release status | none | One current integration baseline; all required CI green; no frozen evidence changed |
| **P0.2** | Define `security_ir` schema + `UNKNOWN`/provenance semantics | P0.1 | Golden fixtures; versioned schema; deterministic validation |
| **P0.3** | Map existing Lean families to six deployment contracts | P0.2 | Kernel-checkable instances; concrete counterexamples; no circular claims |
| **P0.4** | Build read-only Compose extractor + capability graph | P0.2 | Planted bypasses found; uninspected features marked unknown |
| **P0.5** | Deliver `cstack scan/verify/report` | P0.3–4 | Fresh-checkout demo and machine-readable assurance report |
| **P1.1** | Add trusted scoped HTTP/file sink and effect-boundary tests | P0.5 | Independent effect receipts, crash/retry/HALT controls, successful honest use |
| **P1.2** | Implement reviewable remediation/config synthesis | P1.1 | Unsafe original fails; remediated deployment passes scoped negative controls |
| **P1.3** | Formalize supported runtime adapter event contract | P1.1 | Explicit abstraction map and checked selected transition/refinement proof obligations |
| **P1.4** | ControlArena evaluation wrapper and blinded protocol comparison | P1.1–3 | Pinned protocol, usefulness, independent sink outcomes, attribution report |
| **P2** | Kubernetes, WASI, identity/cloud policy, host diversity, attestations | R2 achieved | Separate adapter proof/evidence packages, no cross-platform certification by analogy |

**Suggested first change:** add a repository-root `ARCHITECTURE-DEPLOYMENT-VERIFIER.md` and a schema-only `security_ir/` package. This permits incremental migration without touching historical proof/evidence artifacts. Put a deliberately unsafe Compose example and expected **UNASSURED** result in CI immediately; a successful false-positive *assurance* would be a release-blocking regression.

---

## Final assessment

**Control-stack is approximately at the “theorem library + research/reference enforcement + empirical prototypes” stage, not yet at the “general deployment verifier” stage.** The missing work is less about increasing the number of Lean theorems and more about generating a **sound, provenance-rich interface between real configuration and reusable proofs**, then enforcing an intentionally bounded set of consequential effects.

The stable first product should **make uncertainty explicit**, discover a dangerous bypass in an unfamiliar agent deployment, show a reproducible remediation that closes it, and produce an auditable proof/evidence bundle without declaring the entire compute environment safe. This directly complements Redwood/AISI's empirical control evaluations and DeepMind's coverage/recall/response framing.

**Bottom line:** evolve the existing repo; prioritize a conservative deployment IR, extractor, theorem-instantiation engine and one genuinely closed Linux effect path; ship **R1 static verification**, then **R2 scoped controlled execution**. Defer broad OS neutrality until a narrow end-to-end assurance case is working and independently reviewable.

## Sources and inspection links

**Repository baseline:** [main commit `ed35a41`](https://github.com/jwcodes12/control-stack/commit/ed35a41df99021bc90f46e7d93b3bda6fe2ad5a5), [OVERVIEW.md](https://github.com/jwcodes12/control-stack/blob/main/OVERVIEW.md), [ASSURANCE-LEDGER.md](https://github.com/jwcodes12/control-stack/blob/main/ASSURANCE-LEDGER.md), [COMPLETED.md](https://github.com/jwcodes12/control-stack/blob/main/COMPLETED.md), [ROADMAP.md](https://github.com/jwcodes12/control-stack/blob/main/ROADMAP.md), [trusted stack](https://github.com/jwcodes12/control-stack/tree/main/trusted_stack), [Linux confinement documentation](https://github.com/jwcodes12/control-stack/blob/main/docs/AGENT-LINUX-CONFINEMENT.md), [F6 anytime scope](https://github.com/jwcodes12/control-stack/blob/main/docs/F6-ANYTIME-MONITOR.md), [F8 delegated fleet](https://github.com/jwcodes12/control-stack/blob/main/docs/F8-DELEGATED-FLEET.md), [refinement gaps](https://github.com/jwcodes12/control-stack/blob/main/docs/REFINEMENT-GAPS-2026-10-09.md); [PR #43](https://github.com/jwcodes12/control-stack/pull/43), [PR #41](https://github.com/jwcodes12/control-stack/pull/41).

**Independent background:** [Cedar Lean specification](https://github.com/cedar-policy/cedar-spec), [Batfish](https://github.com/batfish/batfish), [AWS Access Analyzer/Zelkova documentation](https://docs.aws.amazon.com/IAM/latest/UserGuide/access-analyzer-concepts.html), [OPA Conftest](https://github.com/open-policy-agent/conftest), [ControlArena](https://control-arena.aisi.org.uk/), [Google DeepMind AI Control Roadmap announcement](https://deepmind.google/blog/securing-the-future-of-ai-agents/), [WASI release status](https://github.com/bytecodealliance/wasi.dev/blob/main/docs/releases/index.md), [Kubernetes NetworkPolicy host-network limitations](https://kubernetes.io/docs/concepts/services-networking/network-policies/).

**Interpretation note:** External documentation establishes capabilities/limits of candidate components; the particular extraction/enforcement architecture, milestones, effort estimates and acceptance gates above are **recommendations**, not claims that those components are already integrated or formally verified in control-stack.

### R2 handoff Tier 1 update (2026-10-10)

The implementation now has distinct ExtractionFaithful and ProtocolRefinement
premises. ProtocolRefinement.publication is full model–runtime correspondence of
sink effects. Finite configuration checking has full Python/Lean agreement on 26
fixtures and 250 seeded mutations, and 520 additive regressions show no negative
fixture becoming accepted. These tests do not discharge the residual premises or
establish R2; later tiers and release gates remain in deployment/QUEUE.md.
