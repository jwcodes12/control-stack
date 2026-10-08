# Structure plan: work that needs no testing (2026-10-08)

This plan covers work that runs no experiments: paper, Lean and tooling. It makes the project easier to extend and to
check while SC-01 waits on an owner decision (deadline amendment or hardware). Status of everything that exists:
[PRIMITIVES-AND-SCENARIOS.md](PRIMITIVES-AND-SCENARIOS.md). Background: the circle consultation and the adversarial
reviews in `reviews/` concluded that the mathematics is classical. The value is in clear structure, conditional
accounting and refutation, so this plan invests there rather than in more theorems.

> **Check first.** Three GitHub branches already implement parts of A and B. Compare them before building anything:
> - `scenario-architecture-20261008`: fail-closed scenario checker, an index of all 28 scenarios, a theorem inventory
>   with scenario and adversary mappings;
> - `scenario-backbone-20261008`: four scenario bundles, schema checker, adversary taxonomy;
> - `scenario-bundles-static-checker-20261008`: bundles, static multi-axis checker, theorem registry, draft preregs.
>
> Pick or merge one, then rescope this plan to what is still missing. The C items (theory) are likely still open, and
> the new Lean results (Leakage, Gate, GateClients, Lease, Necessity, LeakWitness) must join whichever registry wins.

## A. Organise the project around scenarios (highest value)

1. **One folder per scenario.** Follow the schema already proposed in [SCENARIO-CATALOG.md](SCENARIO-CATALOG.md) §6.
   Each `scenarios/SC-XX/` holds:
   - `scenario.yaml`: bad event, attacker controls, protected assets, observation boundary, horizon, honest task;
   - `claim`: the Lean theorem names it rests on;
   - `policy`: the gate configuration the claim refers to;
   - `correspondence.md`: for each premise, its enforcement, evidence and residual assumption;
   - `manifest.json`: hashes, evidence and multi-axis assumption records;
   - `result.md`;
   - `tests/`: positive and negative cases.

   Migrate SC-01, SC-03 and SC-13/27 first. Today they are scattered across `gateway/`, `egress/`, `auditgate/`,
   `assurance/` and root documents.
   *Acceptance:* each migrated folder validates. The old paths keep working, or are referenced from the new folder.

2. **A generic case checker.** One tool runs on any scenario folder. It generalises `tools/check_sc01_case.py`:
   - it fails closed on a missing field;
   - it reports PROOFS / BINDINGS / EVIDENCE / APPLICABILITY separately;
   - it exits 3 when a hypothesis is refuted;
   - it requires the multi-axis assumption record (provenance, testability, refuting lemma and experiment, scoped
     witness) for every premise;
   - a generator may never mark its own evidence verified.

   *Acceptance:* SC-01 gives the same verdict as the current checker (HYPOTHESIS_REFUTED, exit 3). SC-03 and SC-13/27
   give CONDITIONAL with their premises listed.

3. **Spec-level drafts for the 19 unstarted scenarios.** For each: the bad event, which F1–F8 primitive covers it, a
   thin Lean instantiation, what would refute it, and the honest-task baseline it would need. Several are nearly free
   now that the primitives exist:
   - SC-26 (irreversible transactions) is `GateClients.Approval`;
   - SC-14 (runaway resources) is `Lease`;
   - SC-16 (ship before approval) is `GateClients.Artifact` plus Approval;
   - SC-13 (disabling monitoring or shutdown) is `Gate.withHalt` plus AuditGate.

   *Acceptance:* every catalog row has a `scenario.yaml` marked SPECIFIED, plus a Lean statement or an explicit "no
   formal claim (semantic judgement)".

## B. Restructure the Lean library

4. **Folder layout.** `ControlStack/` is about 45 flat files. Reorganise into:
   - `Core/`: leakage transfer, gate interface, finite-probability helpers;
   - `Families/F1…F8/`;
   - `Scenarios/`: thin instantiations;
   - `Witnesses/`.

   Old module names re-export the new ones, so nothing downstream breaks. Do this once, after the registry (item 5)
   exists, because it touches every import.
   *Acceptance:* `lake build ControlStack` passes, and every old import path still resolves.

5. **A theorem registry.** A generated table (`THEOREMS.md` plus JSON) with one row per theorem:
   - family and scenarios;
   - adversary class;
   - premises;
   - status (proved / ledger-verified / adversarially reviewed);
   - necessity witness and its scope.

   It answers "what do we actually have, and for what attacker" in one place.
   *Acceptance:* generated from the source, not maintained by hand. The checker fails if a manifest cites a theorem
   missing from the registry.

6. **Named adversary classes.** Each file currently quantifies over a different attacker (adversarial review, Opus
   D-verdict). Define a small set and label every theorem with one:
   - non-adaptive;
   - adaptive with feedback;
   - shared seed;
   - side-observing;
   - stateful environment.

   This shows where composing two results is legitimate. It is the prerequisite for any real composition theorem.
   *Acceptance:* every registry row has a class, and composition results state the class they need.

## C. Theory that needs no experiments (each closes a gap a reviewer named)

7. **Policy tampering for EgressGate.** Replace "policy integrity by definition" (`tamperPolicy` is the identity) with
   an explicit tamper model and a trusted-host hypothesis. This closes the oldest open audit finding.
8. **Gate composition.** Prove that two gates sharing state preserve their invariants. Add a confused-deputy theorem
   (the agent uses one gate's trusted operation to bypass another) together with its witness.
9. **Halt liveness.** Prove the halt is processed, under an explicit fairness assumption.
10. **Small completions:**
    - a truncation lemma, so `audit_leak_bound` covers "the first k attack steps unaudited" (review D6);
    - the Lean proof that `LeakWitness` attains 1 − ε (currently by hand);
    - a POSITIVE audit policy under false positives (paced or randomised reservation), the counterpart of
      `Necessity.exhausted_no_audit`.

## D. Consolidate the documentation

11. **One status file.** ROADMAP, STACK, SESSION, HANDOFF, HANDOFF-lean-track and HANDOFF-circle overlap. Generate a
    single status page from the manifests and the registry, and move the rest to an archive.
12. **Preregistration templates, written and frozen now, for when testing resumes:**
    - the SC-01 deadline amendment (scaled by a separately measured guest/host slowdown);
    - the two-instance side-channel probe (`ctrlcert probe` gives the refutation threshold);
    - a lifetime-independence test (for `Necessity.correlated_lifetimes_break_gate`).

## Order

1 → 2 → 5 is the structural backbone. Then 3, then 7 and 8, which are the most useful theory. Then 4 (Lean
reorganisation, once), 6, 9–12.

Nothing here claims new mathematics. The goal is a project whose scope, premises and status anyone can read and check
in one pass.
