# Completion record — control-stack primitive sprint

**Date:** 2026-10-09  
**Repository:** `jwcodes12/control-stack`, merged destination `main`  
**Nature:** narrow runnable reference code, tests, generated Lean source review catalog, and exact infrastructure handoff. **Not operational deployment assurance.**

## Code and review artifacts delivered

- [`trusted_stack/controller.py`](trusted_stack/controller.py) and [`trusted_stack/server.py`](trusted_stack/server.py): a narrow SQLite *release-record* control with distinct agent/reviewer/approver/admin Linux UIDs, verified artifact digest, independent trusted review and approval, nonce/expiry/destination binding, lease and global fixed-unit budgets, revocation and absorbing trusted HALT. All checks and release-event insertion occur under one `BEGIN IMMEDIATE` transaction. It **does not** perform an external effect, act as a syscall interceptor, or protect any program that bypasses the broker.
- [`trusted_stack/client.py`](trusted_stack/client.py): a single-request Unix-socket client; broker obtains UID from Linux `SO_PEERCRED`, not request JSON. [`trusted_stack/README.md`](trusted_stack/README.md) documents setup and trust assumptions.
- [`trusted_stack/test_controller.py`](trusted_stack/test_controller.py), [`trusted_stack/test_audit.py`](trusted_stack/test_audit.py), and [`tools/test_trusted_stack_broker.py`](tools/test_trusted_stack_broker.py): positive/negative/adversarial controls, concurrency/replay, simulated restart and sticky HALT. The broker integration test launches an actual Unix-domain socket service on Linux and uses separate OS UIDs; no external command/deployment is dispatched by the service.
- [`trusted_stack/audit.py`](trusted_stack/audit.py): fixed-horizon hidden uniformly precommitted ideal F6 audit schedule, with exact rational `C(N−k,B)/C(N,B)` miss-probability function and finite exhaustive checks. Its premise is a prechosen attack set not observing audit timing/schedule; it does **not** certify adaptive content selection or imperfect recall.
- [`LEAN-STATEMENTS-NORMAL-FORM.md`](LEAN-STATEMENTS-NORMAL-FORM.md): complete generated catalog of **865 indexed** Lean theorem/lemma *source-level statement headers*, with proof bodies omitted and source positions/family/status retained. [`tools/build_statement_catalog.py`](tools/build_statement_catalog.py) can regenerate and drift-check it. **Source normalization is not Lean elaborated kernel normal form or a human translation of every declaration.** Fully elaborated `#print` types and review of their definitions remain necessary.
- [`ROADMAP.md`](ROADMAP.md): canonical F1–F8 backlog with acceptance criteria, dependencies, and explicit distinctions between offline work and deployed effects.
- **[`VM-HANDOFF.md`](VM-HANDOFF.md): exact detailed handoff for a future higher-access VM environment**: G0–G4 acceptance gates, ARM/TCG versus x86/KVM migration hazards, checkout/preflight commands, guest images/port requirements, 64-lifetime usefulness, security observation coverage, actual F1–F8 effect tests and independent statement review.
- [`reviews/statement-catalog/README.md`](reviews/statement-catalog/README.md): reviewer instructions and priority claim families. Historical `PREREG-*.md` and original evidence receipts remain unchanged.

## Checks run — exact scope and provenance

- [GitHub Actions #37884583572](https://github.com/jwcodes12/control-stack/actions/runs/37884583572), reference test/catalog job **PASS**:
  - 18 Python unit tests for transactional controller and ideal F6 auditing.
  - 5 bounded gateway-model differential checks and 3 VM receiver-payload mutation/shape checks.
  - **13 live Linux SO_PEERCRED broker/role requests** under separate OS UIDs. One genuine positive test writes a single SQLite release record; no external effect.
  - `THEOREM-REGISTRY` drift check: 865 entries. Full catalog regenerated and `--check` passed; catalog includes 865 signatures. No theorem was altered by these changes.
- [Full pinned Lean compilation #37884046450](https://github.com/jwcodes12/control-stack/actions/runs/37884046450) **PASS** for the unchanged Lean source. Newer validation also replayed the same root, with status tracked in its own run; never infer a PASS from a queued or still-running job.
- The external VM and genuine agent-safety work in `VM-HANDOFF.md` **has NOT been executed**. No 64-lifetime KVM usefulness replay, live side-channel certification, actual external effect adapter, trusted anti-rollback anchor, independent human theorem review, or unconditional F1–F8 deployment proof was performed.

## Scope/claims not completed

| Family | What the reference demonstrates | What remains |
|---|---|---|
| F1 | Trusted broker checks authorization before one SQLite release row | Universal syscall/tool/egress/filesystem mediation, policy integrity and trusted deputy coverage |
| F2 | Previously proved finite-view model; existing diff tests | Full side-channel observation correspondence; independently viable native SC-01 guests |
| F3 | Trusted HALT blocks future modeled release rows | Actual OS-level effect freeze and bounded trusted HALT delivery |
| F4 | Digest binding and separate reviewer/approver UIDs | Trusted external artifact deployment, signer, independent attestation and correct content review |
| F5 | Fixed one-unit transactional lease/global counter | Meter actual resources, fork/global worker attribution and anti-rollback/clock trust |
| F6 | Ideal precommitted fixed audit reservation | Formalize/implement imperfect and feedback-adaptive auditing with useful coverage bounds |
| F7 | One-use exact-payload approval with trusted UID separation | Real key custody/signatures, durable anti-replay root and third-party authority |
| F8 | Shared SQLite atomic counters for modeled release | Universal cross-client/multi-agent causal composition including real external effects |

**Scenarios:** 28 total; 3 conditional, 25 draft; **0 deployment-assured**. SC-01 remains *usefulness-failed* in the old ARM64 TCG environment (**0/64 lifetimes baseline and mediated at 0.25 s**), and *model-only/conditional* on full observation premises.

**Unreviewed source scopes:** 821 `UNKNOWN` adversary classifications remain in the registry, many technical lemmas; do not infer theorem semantics from the lexical inventory.

## Where to resume

**Start with [`VM-HANDOFF.md`](VM-HANDOFF.md)** if the next environment has native KVM, guest provisioning, separate OS UIDs, trusted counters, and authority for isolated testing. Follow the go/no-go gates in order, preserve failure evidence, and update the [canonical ROADMAP](ROADMAP.md) and scenario manifests only with actually verified results.

An independent reviewer should use [`LEAN-STATEMENTS-NORMAL-FORM.md`](LEAN-STATEMENTS-NORMAL-FORM.md) as a source index, then obtain elaborated theorem types and inspect their intended threat/observation meaning before approving any inference about real harm.

**Do not mark these primitive families or scenario cases fully complete or deployment assured solely because the tests and Lean source build pass.**
