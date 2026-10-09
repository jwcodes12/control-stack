# Remaining structure and assurance work (updated 2026-10-08)

The architecture from the previous structure plan is integrated on `structure-merge-20261008`. This is **not** a new proof or deployment certification. Canonical links: [ROADMAP.md](ROADMAP.md), [THEOREM-REGISTRY.md](THEOREM-REGISTRY.md), [scenarios/INDEX.md](scenarios/INDEX.md), [comparison.md](reviews/structure-merge/comparison.md).

## Still missing before approving this integration

1. Run `lake exe cache get && lake build ControlStack` on Lean 4.34.0; replay every new `#print axioms`, check only standard axioms and no sorry. Reconcile any import/cycle breakage from the six reviewed module relocations.
2. Run `python3 tools/check_sc01_case.py` unchanged: require steps 1–4 to pass; isolate the expected host-bound `/usr/bin/openssl` cache receipt failure in step 5; do not edit any frozen receipt. Run `python3 tools/test_ctrlcert.py`.
3. Run `python3 tools/check_scenarios.py`, `python3 -m unittest tools.test_check_scenarios`, `python3 tools/build_registry.py --check`, and `python3 tools/build_status.py --check`. Mutate a required assumption axis or a proof reference in a disposable worktree and confirm fail-closed.
4. The inventory is lexical and most declarations have `UNKNOWN` adversary and `UNMAPPED` premises. Review and classify all meaningful theorem statements against [ADVERSARY-CLASSES.md](ADVERSARY-CLASSES.md) before composing results. Lexical registration is not namespace-resolved proof checking.
5. The hardening branch now has an explicit usefulness field per premise and six required scope axes in all 28 manifests. Still needed: independently attested provenance, stronger links between each premise, its falsifier, an executed negative test, and explicit reviewer decisions. Never elevate self-declared receipts to `RUNTIME_VALIDATED` or `DEPLOYMENT_ASSURED`.
6. SC-01: decide hardware isolation vs separately preregistered deadline amendment; repeat only after the owner decision. SC-03: assess permitted deputies and all-destination process attribution; SC-13: check universal mediation and dispatch control; SC-27: build independently rooted evidence/attestation rather than treating an audit theorem as an attestation proof.
7. Fill 25 draft scenarios with narrow falsifiable theorems, credible test fixtures, and honest-task baselines before promoting them from DRAFT. No runtime or negative experiment was performed by the structure merge.

## Still missing theory

- Halt liveness under explicitly stated scheduling/fairness.
- General audit-bound prefix/truncation lemma and a positive false-positive-budget policy.
- Tightness of the leaky audit instance `LeakWitness` (the original text explicitly says the equality is unproved).
- Actual shared-state runtime correspondence and confused-deputy prevention; C's `GateComposition` counterexample shows a gap, not a full enforcement mechanism.
- Policy integrity enforcement outside the Lean transition model; `PolicyTamper` makes the write-authority assumption explicit but cannot attest the OS.

Original preregistrations `PREREG-*.md` and evidence receipts are frozen and were not edited. New *editable* templates and drafts are consolidated under [prereg/](prereg/). The immutable historical root files remain an archival exception.
