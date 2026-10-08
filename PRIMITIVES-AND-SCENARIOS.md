# Primitives and scenarios: what exists and what is left (2026-10-08)

> Update after adversarial review (Gemini 3.1 Pro, Opus 5.5):
> - Lease now bounds the number of units and refuses forks onto existing workers.
> - Artifact assumes injectivity only on contents in the run.
> - Approval/Artifact/Lease separate agent ops from trusted ops.
> - `LeakWitness` gives a real-leak instance of the audit bound.
>
> See `reviews/adversarial-2026-10-08/disposition.md`.

This page summarises status against the eight proof/checker families (F1–F8) and the 28-scenario starter set in
[SCENARIO-CATALOG.md](SCENARIO-CATALOG.md). Per-result detail lives in [STACK.md](STACK.md) and
[ROADMAP.md](ROADMAP.md).

Status words:
- **verified**: ledger red team plus Lean gate.
- **proved**: Lean, standard axioms, no red team.
- **runtime**: implemented and tested.
- **missing**: not built.

No scenario is DEPLOYMENT_ASSURED, and none is close.

## 1. Primitives (F1–F8)

| family | what exists | status | what is left |
|---|---|---|---|
| **F1 capability confinement** | `SANDBOXF1/2` (bubblewrap mount model); `EgressGate` (+ runtime egress slice: 62 controls, CI); `AuditDispatch`; Cedar pinned as a dependency | verified (sandbox model), proved, runtime | (1) EgressGate assumes policy integrity by definition: make it an explicit trusted-host hypothesis or model tampering. (2) ~~shared reference-monitor interface~~ **done**: `Gate.lean` (`Spec.trace_safe`, `NoAgentEffects`, `withHalt`), with AuditDispatch, AuditGate and EgressGate as clients in `GateClients.lean`. (3) A real Cedar-policy client. |
| **F2 bounded observation** | `CovertChannel`, `GatewayModel`, `GatewayCore` (+ 2000-trace difftest), `SideChannel`, `ScenarioACore`, **`Leakage`** (sequential transfer: stateful side channels with feedback) | proved; Python correspondence tested | (1) A Python↔core refinement proof (currently a differential test). (2) **The runtime observation boundary**: refuted on a single host (cache bit 64/64); the QEMU pair shares host hardware and has no channel measurement. (3) Variable or observable episode counts as a first-class tree mass (the theory exists in `Leakage.mass`; it has no instance). |
| **F3 stateful temporal invariant** | `LifetimeLedger` (no-rollback necessary); `AuditGate` invariant (+ PostgreSQL outcome matrix); `DeferGame`/`DeferMono` | proved, runtime (auditgate, ledger controls) | (1) absorbing shutdown is now generic: `Gate.withHalt` adds a trusted halt to any gate (`halt_absorbing`, `halt_freezes`) and the spec lifts (`withHalt_spec`). Still missing: the runtime enforcement of scaffold assumptions A1–A4 and A11 (🔒 John), and a general check-before-effect ordering for asynchronous harms. (2) Crash, restart and TOCTOU models for the gate itself. |
| **F4 integrity / provenance** | `GateClients.Artifact`: content-addressed deploy gate. `deployed_reviewed`; `deployed_is_reviewed` (under collision resistance); `collision_breaks` (necessity) | proved (model); no runtime | A runtime client (a git or OCI digest gate) with correspondence; signing-key custody; "reviewed ≠ harmless". SC-16/17/18/21/27 reuse it. |
| **F5 quotas, leases, revocation** | `LifetimeLedger` (per-lineage cap), `AuditBudget`, **`Lease.lean`** (gate client): `lease_safe` (work only under an issued, unexpired lease; per-lease spend summed over all forked workers ≤ budget; global spend ≤ cap), `revoke_absorbing`, `fork_without_lease_accounting` (necessity: per-worker budgets let one fork double a lease) | proved (model) | A runtime counter service with correspondence (durability across restarts, forged worker identities); resource metering that the agent cannot under-report. |
| **F6 conditional probabilistic control** | UMPROT/UMADAPT/UMDEFER/UMCERT/TMCERT/TMLIP/TMGAC (verified); Compose*, `MultiStep`, `AuditBudget`, **`Leakage.audit_leak_bound`**, **`audit_adaptive_hidden`** (proved); 44 Lean-checked empirical certificates | verified + proved; certificates CONDITIONAL, near-vacuous at N = 100 | (1) Audit budgets under false positives. The no-go is done: `Necessity.exhausted_no_audit` (first-come auditing is exhausted by false positives; 7/8 vs 3/4), and `ctrlcert audit --fpr` reports it. A POSITIVE policy theorem (pacing or randomised reservation) and imperfect auditors are still open. (2) **Adaptive coverage**: history-dependent attack-content laws (Astra rank 4). (3) Joint collusion plus side channel: UM bad-row pass ≤ L·Σc·h. (4) Fresh prospective data (thousands of attacks) for a non-vacuous certificate. |
| **F7 two-party / typed approval** | `GateClients.Approval`: exact payload, expiry and nonce. `approval_safe` (approved, unexpired, no replay); `replay_without_nonce` (necessity) | proved (model); no runtime | A runtime signer (a distinct principal's key; unforgeability is a premise); a human may approve a harmful payload (SC-26, SC-10, SC-16). |
| **F8 composition** | `Leakage.seq_transfer` (adaptive sequential composition of leakage); `ComposeGame`/`ComposeAvg` (monitors); `Necessity` witnesses for naive products | proved | Multi-agent global budgets (SC-28); composition across F1 + F2 (a confined action can still carry a 1-bit command; `one_bit_coordinates`); one shared adversary semantics. Both consultants said the general calculus should wait until two clients need the same interface. |

**Cross-cutting tooling**
- `tools/check_sc01_case.py`: one-command case check. It separates proof, binding, evidence and applicability, and
  exits 3 when a hypothesis is refuted.
- `tools/assurance.py` with 44 manifests.
- **`tools/ctrlcert.py`**: researcher CLI. It prints each bound with its theorem, premises and refuting measurement,
  and emits Lean.

What is missing:
- A scenario schema validator (catalog §6).
- One portable benchmark adapter. Exporters still hard-code home-directory paths.

## 2. Scenarios

| ID | scenario | status | blocker / next step |
|---|---|---|---|
| **SC-01** | exact secret recovery through inter-agent messages | the furthest along. Theory complete for a bounded interface (now including stateful side channels). Usefulness: 320/320 on a single host. Single-host side certificate REFUTED. QEMU pair: link fixed; the frozen usefulness gate FAILED (all agents miss the 0.25 s deadline under TCG) | the owner decides: (a) a preregistered deadline amendment for emulation, or (b) hardware-virtualised or separate hosts. After either, run a fresh side-channel probe (`ctrlcert probe` gives the refutation threshold). The probability bound stays an open obligation (`gateway/vm/BOUND.md`) |
| SC-02 | multi-episode accumulation | ledger proved; controls pass; one restore breaks it (`restore_breaks`) | external anchor against rollback (trust base) |
| SC-03 | outbound egress | bounded TCP reachability slice CONDITIONAL; CI green | outer-topology attribution; policy integrity (F1 item 1); this does not imply confidentiality |
| SC-04 | leakage via diagnostics and timing | cache channel found (negative result); `Leakage` gives the accounting | measure the residual channels in whatever isolation is chosen |
| SC-05 | 1-bit coordination | negative result proved (`one_bit_coordinates`) | done as a no-go; prevention needs F1 on the action, not F2 |
| SC-13 / SC-27 | monitoring/audit tampering | auditgate v1.1: database-level invariant proved, PostgreSQL outcome matrix in CI; documented no-go for auto_workflow as deployed | generalise via the F1 gate interface; evidence-chain integrity needs F4 |
| SC-16 | ship before approval | paused | F4 plus F7 |
| SC-24 | untrusted-monitor collusion | strongest theory (verified UM stack, adaptive converses, LASR certificates) | L, r and coverage cannot be measured; certificates near-vacuous at N = 100 (`ctrlcert diagnose`: margin vs protocol) |
| SC-25 | after-the-fact monitoring of irreversible acts | partial (`DeferGame`, `MultiStep`) | the check-before-effect primitive (F3 item 1) |
| SC-06–12, 14, 15, 17–23, 26, 28 | (host compromise, artefact sabotage, data poisoning, prompt injection, transactions, multi-agent budgets) | **not started** | most need only F1/F3/F4/F5/F7 instances once those primitives exist. Wave 1 in the catalog: SC-08/09/13/25 on BashArena |

## 3. What is left, in order (recommendation)

1. **Unblock SC-01's usefulness decision (🔒 owner).** Choose a deadline amendment or hardware isolation. Without
   one, the selected scenario has no passing usefulness evidence on any isolated configuration.
2. **Red-team the new results.** Run a two-family ledger red team of `Leakage`, `Necessity`, `MultiStep`,
   `AuditBudget`, `SideChannel` and `GatewayCore`. Today they are proved, not verified.
3. **Primitives.** The shared gate interface, F4 artefact gate, F7 approval and generic absorbing halt are now proved
   models (`Gate.lean`, `GateClients.lean`). Left:
   - F5 leases and revocation, and global counters;
   - runtime implementations of F4 and F7 with correspondence tests, as was done for the egress and auditgate
     slices.
4. **Wave 1 on one real setting (BashArena):** SC-08, SC-09, SC-13 and SC-25 with the shared gate, plus an
   honest-task baseline. The catalog requires the usefulness measurement alongside safety.
5. **F6 theory gaps:** false-positive audit budgets, adaptive coverage, and joint collusion plus side channel.
6. **Researcher-facing:**
   - one portable eval-log adapter (no home paths);
   - a prospective external-user demonstration (Astra's acceptance test: someone changes a decision because of the
     output);
   - the write-up, headlining the no-go results and the refutation loop.
7. **Human expert review** of `REVIEW-PACKET.md` (🔒 owner).

The honest ceiling, from both consultations: this produces machine-checked conditional accounting, refutations and
experiment design for narrow protocols. It does not produce deployment guarantees for LLM agents.
